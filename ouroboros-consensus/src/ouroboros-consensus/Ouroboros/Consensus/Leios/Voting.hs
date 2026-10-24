{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Voting for endorser blocks, with the BLS keys of the node's credentials.
--
-- The node votes for an endorser block once it has its closure, if the tip
-- of its selection announced it, one of its keys holds a seat in the
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
import Control.Monad (forever, void)
import Control.Monad.Except (runExcept)
import Control.ResourceRegistry (forkLinkedThread, withRegistry)
import Control.Tracer (Tracer, traceWith)
import Data.ByteString (ByteString)
import Data.Foldable (for_)
import Data.Proxy (Proxy (..))
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Traversable (for)
import Data.Void (Void)
import Ouroboros.Consensus.Block
  ( BlockProtocol
  , ConvertRawHash
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
import Ouroboros.Consensus.Ledger.Abstract (ComputeLedgerEvents (OmitLedgerEvents), applyChainTick)
import Ouroboros.Consensus.Ledger.Extended (ledgerState)
import Ouroboros.Consensus.Ledger.SupportsEndorserBlocks (LedgerSupportsEndorserBlocks (..))
import Ouroboros.Consensus.Ledger.SupportsMempool (LedgerSupportsMempool (..))
import Ouroboros.Consensus.Ledger.SupportsProtocol (LedgerSupportsProtocol, ledgerViewForecastAt)
import Ouroboros.Consensus.Leios.AnnounceState (AnnounceState, isEquivocated)
import Ouroboros.Consensus.Leios.Protocol
  ( LeiosAnnouncement (..)
  , LeiosLedgerView (..)
  , LeiosProtocol (..)
  )
import Ouroboros.Consensus.Leios.Types
  ( LeiosPoint (..)
  , LeiosVote (..)
  , RankingBlockHash
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
  , voterClosure :: LeiosPoint -> m (Maybe [ByteString])
  -- ^ The transactions of the closure at a point, if the node has them all.
  , voterAnnounceState :: AnnounceState m blk
  , voterVoteState :: VoteState m blk
  , voterSystemTime :: SystemTime m
  , voterTracer :: Tracer m TraceLeiosVoting
  }

-- | What the voter traces.
data TraceLeiosVoting
  = -- | The node applied the closure of an endorser block, and may vote for it.
    TraceLeiosEbValidated !LeiosPoint
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
  | -- | The tip of the node's selection did not announce the block by the end
    -- of the window to vote.
    TipDoesNotAnnounce
  | -- | The node has no complete closure of the block after all.
    ClosureUnavailable
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
                  validate announcing >>= \case
                    Left reason -> pure (Left reason)
                    Right () -> do
                      traceWith voterTracer (TraceLeiosEbValidated point)
                      waitUntil (voteFrom window)
                      cast announcing
     where
      seats = [(key, seat) | key <- keys, Just seat <- [getLeiosSeatId (deriveVerKeyDSIGN key) llvCommittee]]

      window = leiosVoteWindow view onset

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
    , voterClosure
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

  -- Apply the closure to the ledger state of the announcing block.
  validate announcing =
    voterClosure point >>= \case
      Nothing -> pure (Left ClosureUnavailable)
      Just closure ->
        bracket
          (ChainDB.openReadOnlyForkerAtPoint voterChainDB (SpecificPoint (headerPoint (ancHeader announcing))))
          (either (const (pure ())) roforkerClose)
          $ \case
            -- The selection moved off the announcing block meanwhile.
            Left _ -> pure (Left TipDoesNotAnnounce)
            Right forker -> do
              extLedger <- atomically $ roforkerGetLedgerState forker
              let lcfg = configLedger voterConfig
                  ticked = applyChainTick OmitLedgerEvents lcfg slot (ledgerState extLedger)
              case traverse (decodeEbTx ticked) closure of
                Left err -> pure (Left (EbInvalid err))
                Right txs -> do
                  let keySets = foldMap getTransactionKeySets txs
                  values <- roforkerReadTables forker keySets
                  pure $
                    either (Left . EbInvalid . Text.pack . show) Right . runExcept $
                      applyEbTxs lcfg slot txs (applyMempoolDiffs values keySets ticked)

  waitUntil at = do
    now <- systemTimeCurrent voterSystemTime
    threadDelay (nominalDelay (diffRelTime at now))

-- | Sign a vote for an announcement in a seat.
signVote :: LeiosSigningKey -> LeiosSeatId -> RankingBlockHash -> LeiosVote
signVote key seat rbHash =
  MkLeiosVote
    { voteAnnouncingRbHash = rbHash
    , voteSeatId = seat
    , voteSignature = signDSIGN leiosSignContext rbHash key
    }
