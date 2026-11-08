{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Voting for endorser blocks, with the BLS keys of the node's credentials.
--
-- The node votes for an endorser block once it has its closure, if the tip
-- of its selection announced it, the node accepted that announcement within
-- L_hdr and no other of the election, one of its keys holds a seat in the
-- election, and the closure applies to the tip's ledger state. It votes once
-- the window to vote opens, if by then it saw no other announcement of the
-- election, the tip still announces it, and the window has not closed.
--
-- Each endorser block gets a thread of its own, so a closure that takes long
-- to validate delays no other block's vote. And the closure is validated as
-- soon as it is complete, rather than once the window opens, which leaves
-- the window to the vote.
module Ouroboros.Consensus.Leios.Voting
  ( LeiosVoterEnv (..)
  , LeiosVoterTxCache (..)
  , noLeiosVoterTxCache
  , TraceLeiosVoting (..)
  , NotVotedReason (..)
  , runLeiosVoter
  ) where

import Cardano.Crypto.DSIGN (deriveVerKeyDSIGN, signDSIGN)
import Cardano.Crypto.Leios
  ( LeiosSeatId
  , LeiosSigningKey
  , getLeiosSeatId
  , leiosSignContext
  )
import Cardano.Ledger.BaseTypes (unboundRational)
import Cardano.Ledger.Dijkstra (DijkstraEra)
import Control.Monad (forever, void)
import Control.Monad.Except (runExcept)
import Control.ResourceRegistry (forkLinkedThread, withRegistry)
import Control.Tracer (Tracer, traceWith)
import Data.Bifunctor (first)
import Data.Foldable (for_)
import qualified Data.Map.Strict as Map
import qualified Data.Measure as Measure
import Data.Proxy (Proxy (..))
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Time (NominalDiffTime)
import Data.Traversable (for)
import Data.Void (Void)
import Ouroboros.Consensus.Block
  ( BlockProtocol
  , ConvertRawHash
  , SlotNo
  , blockSlot
  , headerPoint
  )
import Ouroboros.Consensus.BlockchainTime.WallClock.Types
  ( SystemTime (..)
  , addRelTime
  , diffRelTime
  )
import Ouroboros.Consensus.Config (TopLevelConfig, configLedger)
import Ouroboros.Consensus.Forecast (forecastFor)
import Ouroboros.Consensus.HardFork.Abstract (HasHardForkHistory (..))
import qualified Ouroboros.Consensus.HardFork.History as HardFork
import Ouroboros.Consensus.Ledger.Abstract
  ( ComputeLedgerEvents (OmitLedgerEvents)
  , LedgerConfig
  , applyChainTick
  )
import Ouroboros.Consensus.Ledger.Basics (TickedLedgerState)
import Ouroboros.Consensus.Ledger.Extended (ledgerState)
import Ouroboros.Consensus.Ledger.SupportsEndorserBlocks (LedgerSupportsEndorserBlocks (..))
import Ouroboros.Consensus.Ledger.SupportsMempool
  ( ByteSize32 (..)
  , GenTx
  , LedgerSupportsMempool (..)
  , TxEbMeasureByteSize (..)
  , TxLimits (..)
  , TxMeasure (..)
  , WhetherToIntervene (Intervene)
  )
import Ouroboros.Consensus.Ledger.SupportsProtocol (LedgerSupportsProtocol, ledgerViewForecastAt)
import Ouroboros.Consensus.Ledger.Tables
  ( DiffMK (..)
  , HasLedgerTables (..)
  , KeysMK (..)
  , LedgerTables
  , ValuesMK (..)
  , ltliftA2
  , ltliftA3
  )
import Ouroboros.Consensus.Ledger.Tables.Diff (Delta (..), Diff (..))
import Ouroboros.Consensus.Ledger.Tables.Utils (forgetLedgerTables, restrictValuesMK)
import Ouroboros.Consensus.Leios.AnnounceState
  ( AnnounceState
  , acceptedAnnouncementAge
  , isEquivocated
  )
import Ouroboros.Consensus.Leios.Protocol
  ( LeiosAnnouncement (..)
  , LeiosLedgerView (..)
  , LeiosProtocol (..)
  )
import Ouroboros.Consensus.Leios.Types
  ( LeiosPoint (..)
  , LeiosVote (..)
  , ProtVerParity
  , RankingBlockHash
  , TxHash
  , deserialiseEndorserBlock
  , endorserBlockReferences
  , milliseconds32ToNominalDiffTime
  )
import Ouroboros.Consensus.Leios.VoteState (AddVoteResult (..), VoteState, addVote)
import Ouroboros.Consensus.MiniProtocol.LeiosNotify.Client.Announcements.Validation
  ( AnnouncingHeader (..)
  , announcingRbHash
  , mkAnnouncingHeader
  )
import Ouroboros.Consensus.MiniProtocol.LeiosNotify.Client.State
  ( AcceptedVote (..)
  , VoteWindow (..)
  , leiosVoteWindow
  )
import Ouroboros.Consensus.Storage.ChainDB.API (ChainDB)
import qualified Ouroboros.Consensus.Storage.ChainDB.API as ChainDB
import Ouroboros.Consensus.Storage.LedgerDB.Forker (ReadOnlyForker (..))
import Ouroboros.Consensus.Storage.LeiosDB.API
  ( LeiosDbHandle
  , LeiosDbReader (..)
  , withReader
  )
import Ouroboros.Consensus.Util.IOLike
  ( IOLike
  , MonadAsync (race)
  , MonadDelay (threadDelay)
  , STM
  , atomically
  , bracket
  , retry
  )
import Ouroboros.Consensus.Util.Time (nominalDelay)
import qualified Ouroboros.Network.AnchoredFragment as AF
import Ouroboros.Network.Protocol.LocalStateQuery.Type (Target (SpecificPoint))

-- | What the node's voter needs.
data LeiosVoterEnv m blk = MkLeiosVoterEnv
  { voterConfig :: TopLevelConfig blk
  , voterChainDB :: ChainDB m blk
  , voterLeiosDb :: LeiosDbHandle m
  , voterTxCache :: LeiosVoterTxCache m
  , voterAnnounceState :: AnnounceState m blk
  , voterVoteState :: VoteState m blk
  , voterSystemTime :: SystemTime m
  , voterTracer :: Tracer m TraceLeiosVoting
  }

-- | Which transactions the node validated already, and under which protocol
-- version parity, as the LeiosTxCache is to tell.
data LeiosVoterTxCache m = MkLeiosVoterTxCache
  { lookupValidatedTxs :: [TxHash] -> m [Maybe ProtVerParity]
  -- ^ For each transaction, the parity it was validated under, if it was.
  , insertValidatedTxs :: ProtVerParity -> [TxHash] -> m ()
  -- ^ Record that the node validated these transactions under this parity.
  }

-- | Knows of no validated transaction, and records none.
noLeiosVoterTxCache :: Applicative m => LeiosVoterTxCache m
noLeiosVoterTxCache =
  MkLeiosVoterTxCache
    { lookupValidatedTxs = pure . map (const Nothing)
    , insertValidatedTxs = \_parity _txHashes -> pure ()
    }

-- | What the voter traces.
data TraceLeiosVoting
  = -- | The node applied the closure of an endorser block, and may vote for it:
    -- it reapplied that many transactions it validated before, and validated
    -- the others in full.
    TraceLeiosEbValidated
      !LeiosPoint
      -- | reapplied
      !Int
      -- | validated in full
      !Int
  | -- | The node voted for the endorser block of an announcement.
    TraceLeiosVoted !LeiosVote
  | TraceLeiosNotVoted !LeiosPoint !NotVotedReason
  deriving Show

-- | Why the node did not vote for an endorser block.
data NotVotedReason
  = -- | The node has no ledger view of the election slot, or it has no Leios.
    NoLeiosLedgerView
  | -- | None of the node's BLS keys holds a seat in the election.
    NotOnCommittee
  | -- | The node accepted no announcement of the block from a peer within
    -- L_hdr after the election slot began.
    NotAccepted
  | -- | The node accepted the announcement of the block this long after the
    -- election slot began, later than L_hdr.
    AnnouncedLate !NominalDiffTime
  | -- | The tip of the node's selection did not announce the block by the end
    -- of the window to vote.
    TipDoesNotAnnounce
  | -- | The node holds no body of the block after all.
    BodyUnavailable
  | -- | The node has no complete closure of the block after all.
    ClosureUnavailable
  | -- | The block references more than an endorser block may hold, by what it
    -- claims of its transactions or by what they turn out to take.
    EbOverCapacity
  | -- | The closure does not apply to the tip's ledger state.
    EbInvalid !Text
  | -- | The node saw another announcement of the election.
    Equivocated
  | -- | The window to vote closed before the node was ready to.
    TooLate
  | -- | The node's 'VoteState' did not add the node's own vote.
    VoteNotAdded !AddVoteResult
  deriving (Eq, Show)

-- | Vote for each endorser block the given action yields, once the node has
-- its closure.
runLeiosVoter ::
  forall m blk.
  ( IOLike m
  , LedgerSupportsProtocol blk
  , LedgerSupportsEndorserBlocks blk
  , HasHardForkHistory blk
  , ConvertRawHash blk
  ) =>
  LeiosVoterEnv m blk ->
  [LeiosSigningKey] ->
  -- | The next point whose closure the node acquired
  STM m LeiosPoint ->
  m Void
runLeiosVoter env keys acquired =
  withRegistry $ \registry ->
    forever $ do
      point <- atomically acquired
      void . forkLinkedThread registry "Leios.voteFor" $
        voteFor env keys point >>= \case
          Left reason -> traceWith (voterTracer env) (TraceLeiosNotVoted point reason)
          Right votes -> for_ votes $ traceWith (voterTracer env) . TraceLeiosVoted

-- | Vote for an endorser block with every key that holds a seat in its
-- election.
voteFor ::
  forall m blk.
  ( IOLike m
  , LedgerSupportsProtocol blk
  , LedgerSupportsEndorserBlocks blk
  , HasHardForkHistory blk
  , ConvertRawHash blk
  ) =>
  LeiosVoterEnv m blk ->
  [LeiosSigningKey] ->
  LeiosPoint ->
  m (Either NotVotedReason [LeiosVote])
voteFor env keys point@MkLeiosPoint{pointSlotNo = slot} = do
  immLedger <- atomically $ ChainDB.getImmutableLedger voterChainDB
  case electionAt immLedger of
    Nothing -> pure (Left NoLeiosLedgerView)
    Just (view@MkLeiosLedgerView{llvCommittee, llvQuorumStakeThreshold}, onset)
      | null seats -> pure (Left NotOnCommittee)
      | otherwise -> do
          acquired <- systemTimeCurrent voterSystemTime
          if acquired > votingEnds
            then pure (Left TooLate)
            else
              -- Wait for the selection to adopt the announcing block, if it has
              -- not yet.
              race (waitUntil votingEnds) (atomically tipAnnouncing) >>= \case
                Left () -> pure (Left TipDoesNotAnnounce)
                Right announcing ->
                  acceptance announcing >>= \case
                    Left reason -> pure (Left reason)
                    Right () ->
                      validate announcing >>= \case
                        Left reason -> pure (Left reason)
                        Right (reapplied, applied) -> do
                          traceWith voterTracer (TraceLeiosEbValidated point reapplied applied)
                          waitUntil (voteFrom window)
                          cast announcing
     where
      seats = [(key, seat) | key <- keys, Just seat <- [getLeiosSeatId (deriveVerKeyDSIGN key) llvCommittee]]

      window = leiosVoteWindow view onset

      -- The announcing block's header must have arrived within L_hdr, and the
      -- node must have seen no other announcement of the election by then.
      acceptance announcing = do
        known <- atomically $ acceptedAnnouncementAge voterAnnounceState announcing
        acceptedBy <- case known of
          Just age -> pure (Right age)
          Nothing -> race (waitUntil onTimeUntil) (atomically (acceptedAge announcing))
        case acceptedBy of
          Left () -> pure (Left NotAccepted)
          Right age -> do
            equivocated <- atomically $ isEquivocated voterAnnounceState announcing
            pure $
              if
                | age > lHdr -> Left (AnnouncedLate age)
                | equivocated -> Left Equivocated
                | otherwise -> Right ()

      lHdr = milliseconds32ToNominalDiffTime (llvAnnouncementPeriod view)

      onTimeUntil = addRelTime lHdr onset

      -- The voting period ends L_vote after the window opens.
      votingEnds = addRelTime (milliseconds32ToNominalDiffTime (llvVotePeriod view)) (voteFrom window)

      cast announcing = do
        now <- systemTimeCurrent voterSystemTime
        (stillAnnounces, equivocated) <-
          atomically $
            (,) <$> (Just announcing ==) <$> tipAnnouncing' <*> isEquivocated voterAnnounceState announcing
        if
          | now > votingEnds -> pure (Left TooLate)
          | not stillAnnounces -> pure (Left TipDoesNotAnnounce)
          | equivocated -> pure (Left Equivocated)
          | otherwise -> do
              results <- for seats $ \(key, seat) -> do
                let vote = signVote key seat (announcingRbHash announcing)
                result <- addVote voterVoteState voterSystemTime (accepted vote)
                pure (vote, result)
              pure $ case [vote | (vote, Added) <- results] of
                [] | (_, result) : _ <- results -> Left (VoteNotAdded result)
                votes -> Right votes

      accepted vote =
        MkAcceptedVote
          { acceptedVote = vote
          , voteElectionSlot = slot
          , voteCommittee = llvCommittee
          , acceptedQuorum = unboundRational llvQuorumStakeThreshold
          , voteWindow = window
          }
 where
  MkLeiosVoterEnv
    { voterConfig
    , voterChainDB
    , voterLeiosDb
    , voterTxCache
    , voterAnnounceState
    , voterVoteState
    , voterSystemTime
    , voterTracer
    } = env

  -- The election's ledger view and when its slot began.
  electionAt immLedger = do
    view <-
      either (const Nothing) Just . runExcept $
        forecastFor (ledgerViewForecastAt (configLedger voterConfig) (ledgerState immLedger)) slot
    leiosView <- getLeiosLedgerView (Proxy @(BlockProtocol blk)) view
    (onset, _slotLength) <-
      either (const Nothing) Just $
        HardFork.runQuery
          (HardFork.slotToWallclock slot)
          (hardForkSummary (configLedger voterConfig) (ledgerState immLedger))
    pure (leiosView, onset)

  acceptedAge announcing =
    acceptedAnnouncementAge voterAnnounceState announcing >>= maybe retry pure

  -- The tip of the selection, if it announces the block.
  tipAnnouncing = tipAnnouncing' >>= maybe retry pure

  tipAnnouncing' = do
    chain <- ChainDB.getCurrentChain voterChainDB
    pure $ case AF.head chain of
      Right tip
        | blockSlot tip == slot
        , Just announcing <- mkAnnouncingHeader voterConfig tip
        , announcementEbHash (ancAnnouncement announcing) == pointEbHash point ->
            Just announcing
      _ -> Nothing

  -- Check the endorser block against what one may hold, then apply its
  -- closure to the ledger state of the announcing block.
  validate announcing =
    withReader voterLeiosDb $ \reader ->
      lookupEbBody reader point >>= \case
        Nothing -> pure (Left BodyUnavailable)
        Just body -> case deserialiseEndorserBlock (Proxy @DijkstraEra) body of
          Left err -> pure (Left (EbInvalid (Text.pack (show err))))
          Right eb ->
            bracket
              (ChainDB.openReadOnlyForkerAtPoint voterChainDB (SpecificPoint (headerPoint (ancHeader announcing))))
              (either (const (pure ())) roforkerClose)
              $ \case
                -- The selection moved off the announcing block meanwhile.
                Left _ -> pure (Left TipDoesNotAnnounce)
                Right forker -> do
                  extLedger <- atomically $ roforkerGetLedgerState forker
                  let ticked = applyChainTick OmitLedgerEvents lcfg slot (ledgerState extLedger)
                      capacity = ebCapacityTxMeasure lcfg ticked
                      references = endorserBlockReferences eb
                  if claimedBytes references > toInteger (unByteSize32 (txEbMeasureByteSize capacity))
                    then pure (Left EbOverCapacity)
                    else
                      lookupEbClosure reader point >>= \case
                        Just closure
                          | length closure == length references ->
                              case traverse (decodeEbTx ticked) closure of
                                Left err -> pure (Left (EbInvalid err))
                                Right txs -> do
                                  let txKeys = foldMap getTransactionKeySets txs
                                      txHashes = map fst references
                                      parity = ebTxsProtVerParity ticked
                                  values <- roforkerReadTables forker txKeys
                                  validatedUnder <- lookupValidatedTxs voterTxCache txHashes
                                  let MkClosureOutcome{closureVerdict, closureReapplied, closureApplied} =
                                        applyClosure
                                          lcfg
                                          slot
                                          capacity
                                          (applyMempoolDiffs values txKeys ticked)
                                          (zip3 txHashes (map (== Just parity) validatedUnder) txs)
                                  insertValidatedTxs voterTxCache parity closureApplied
                                  pure $ (closureReapplied, length closureApplied) <$ closureVerdict
                        _ -> pure (Left ClosureUnavailable)

  lcfg = configLedger voterConfig

  claimedBytes references = sum [toInteger size | (_txHash, size) <- references]

  waitUntil at = do
    now <- systemTimeCurrent voterSystemTime
    threadDelay (nominalDelay (diffRelTime at now))

-- | What 'applyClosure' made of a closure.
data ClosureOutcome = MkClosureOutcome
  { closureVerdict :: !(Either NotVotedReason ())
  , closureReapplied :: !Int
  -- ^ How many transactions it reapplied, as the node validated them before.
  , closureApplied :: ![TxHash]
  -- ^ The transactions it validated in full, before the verdict.
  }

-- | Apply the transactions of a closure, one after the other, to the ledger
-- state of the block that announced it, ticked to its slot, as a certificate
-- for it would. And sum what they take of an endorser block's capacity, which
-- must hold them all.
--
-- A transaction the node validated before is reapplied: only the checks that
-- depend on the ledger state run again. Any other is applied with
-- 'Intervene', so that the ledger does not flip a transaction's validity
-- flag, which applying a certified closure would not either.
--
-- The closure's ledger table stays outside the state. Each transaction runs on
-- a state holding only its own inputs, as the mempool runs it, and its effect
-- is folded back into the table, so each step costs what the transaction
-- does, not what the closure does.
applyClosure ::
  forall blk.
  LedgerSupportsEndorserBlocks blk =>
  LedgerConfig blk ->
  SlotNo ->
  -- | What an endorser block may hold
  TxEbMeasure blk ->
  TickedLedgerState blk ValuesMK ->
  -- | Each transaction, with whether the node validated it before
  [(TxHash, Bool, GenTx blk)] ->
  ClosureOutcome
applyClosure cfg slot capacity st0 = go st0 (projectLedgerTables st0) Measure.zero 0 []
 where
  go ::
    TickedLedgerState blk mk ->
    LedgerTables blk ValuesMK ->
    TxEbMeasure blk ->
    Int ->
    [TxHash] ->
    [(TxHash, Bool, GenTx blk)] ->
    ClosureOutcome
  go _ _ _ !reapplied applied [] = MkClosureOutcome (Right ()) reapplied applied
  go st values measured !reapplied applied ((txHash, validated, tx) : txs) =
    case measure of
      Left reason -> stop reapplied (Left reason)
      Right measured' -> case (validated, assumeValidatedEbTx cfg slot stTx tx) of
        (True, Just vtx) -> case runExcept (reapplyTx cfg slot vtx stTx) of
          Left err -> stop reapplied (invalid err)
          Right st' ->
            go
              st'
              (ltliftA3 rebase values txKeys (projectLedgerTables st'))
              measured'
              (reapplied + 1)
              applied
              txs
        _ -> case runExcept (applyTx cfg Intervene slot tx stTx) of
          Left err -> stop reapplied (invalid err)
          Right (st', _vtx) ->
            go
              st'
              (ltliftA2 applyDelta values (projectLedgerTables st'))
              measured'
              reapplied
              (txHash : applied)
              txs
   where
    stop reapplied' verdict = MkClosureOutcome verdict reapplied' applied

    txKeys = getTransactionKeySets tx

    stTx = st `withLedgerTables` ltliftA2 restrictValuesMK values txKeys

    measure = do
      phase1 <- first showInvalid . runExcept $ txMeasurePhase1 cfg (forgetLedgerTables stTx) tx
      phase2 <- first showInvalid . runExcept $ txMeasurePhase2 cfg stTx tx
      let measured' = measured `Measure.plus` txEbMeasure (Proxy @blk) (TxMeasure phase1 phase2)
      if measured' Measure.<= capacity then Right measured' else Left EbOverCapacity

  invalid = Left . showInvalid

  showInvalid = EbInvalid . Text.pack . show

  -- After a reapplied transaction: what 'reapplyTx' left of the transaction's
  -- own entries replaces them in the table. The inputs it consumed are gone,
  -- the ones it only read stay, and its outputs are new.
  rebase :: Ord k => ValuesMK k v -> KeysMK k v -> ValuesMK k v -> ValuesMK k v
  rebase (ValuesMK m) (KeysMK ks) (ValuesMK after) = ValuesMK (Map.union after (Map.withoutKeys m ks))

  -- After an applied transaction: one update per key it changed, where
  -- 'applyDiffs' would merge over the whole table.
  applyDelta :: Ord k => ValuesMK k v -> DiffMK k v -> ValuesMK k v
  applyDelta (ValuesMK m) (DiffMK (Diff ds)) = ValuesMK (Map.foldlWithKey' step m ds)
   where
    step acc k (Insert v) = Map.insert k v acc
    step acc k Delete = Map.delete k acc

-- | Sign a vote for an announcement in a seat.
signVote :: LeiosSigningKey -> LeiosSeatId -> RankingBlockHash -> LeiosVote
signVote key seat rbHash =
  MkLeiosVote
    { voteAnnouncingRbHash = rbHash
    , voteSeatId = seat
    , voteSignature = signDSIGN leiosSignContext rbHash key
    }
