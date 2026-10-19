import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSelectionDisposal

/-! Fixed original DEAD cleanup and repayment prefixes. The saved world is
the entry of a named failed source interval, never a reconstructed Stop world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch

inductive DeadAction where
  | key (key : KeypairId)
  | peerCut (peer : Option PeerId)
  | peerFinish (value : Option (PeerId × Peer))

def DeadAction.source : DeadAction → PrefixM CausalJournal.Event Unit
  | .key keypair => Admission.actualOps.access (keypairPutPrefix (some keypair) false)
  | .peerCut peer => do
      _ ← liftWGObserver (PeerRelease.cut peer)
      pure ()
  | .peerFinish value => PeerRelease.finish value

structure DeadCut where
  ledger : Ledger
  debts : List CleanupDebt
  locals : List TxLocalBatch
  world : World
  before : List CausalJournal.Event
  action : DeadAction

def DeadCut.Valid (cut : DeadCut) (reason : Stop) (last : List CausalJournal.Event) : Prop :=
  Accounted cut.before cut.ledger cut.debts cut.locals cut.world.wg ∧
  runPrefix cut.action.source cut.world cut.before = (.error reason,last) ∧
  Accounted last cut.ledger cut.debts cut.locals cut.world.wg

def deadRepaymentPrefix (pid : PeerId) (key : KeypairId) : RepaymentStage → PrefixM CausalJournal.Event Unit
  | .key => pure ()
  | .peer => Admission.actualOps.access (keypairPutPrefix (some key) false)
  | .finish => do
      Admission.actualOps.access (keypairPutPrefix (some key) false)
      _ ← recordedPeerCut (some pid)
      pure ()

def deadPrefix (pid : PeerId) (items : List SkbId) (head : DataPacket) (stage : RepaymentStage) :
    PrefixM CausalJournal.Event Unit := do
  CreateDisposal.loop (.deadBatch pid head) items
  deadRepaymentPrefix pid head.keypair stage

def workerDeadPrefix (pid : PeerId) (stage : RepaymentStage) : PrefixM CausalJournal.Event Unit := do
  let selected ← workerSelection pid
  match selected with
  | none => pure ()
  | some picked =>
    if picked.crypted then pure ()
    else deadPrefix pid picked.items picked.head stage

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
