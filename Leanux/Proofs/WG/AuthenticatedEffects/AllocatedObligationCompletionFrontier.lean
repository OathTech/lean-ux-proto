import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionBatchSource
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalDebtCleanup

/-! Explicit local completion cursors. A stopped frontier has a real native
callback run, a retained cut world and remaining caller-local ownership. The
callback contract must derive that cut from its actual source; these types
are not an initialized reachability or global conservation assertion. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity HandshakeSecurity.StagedDisposal

structure Binding where
  skb : SkbId
  ticket : Ticket
  position : Nat
  ordinal : Nat
  generation : Nat
  value : DataPacket

def Binding.recorded (binding : Binding) (history : List CausalJournal.Event) : Prop :=
  Origin history binding.position binding.ordinal binding.generation binding.skb binding.value

def Binding.pending (binding : Binding) (ledger : Ledger) : Prop :=
  (binding.ticket,Status.pending (.allocated binding.position binding.ordinal)) ∈ ledger

def Binding.debt (binding : Binding) (ledger : Ledger) (debts : List CleanupDebt) : Prop :=
  ∃ outcome, (⟨binding.ticket,binding.position,binding.ordinal,outcome⟩ : CleanupDebt) ∈ debts ∧
    (binding.ticket,Status.terminal outcome) ∈ ledger

def Binding.terminal (binding : Binding) (ledger : Ledger) : Prop :=
  ∃ outcome, (binding.ticket,Status.terminal outcome) ∈ ledger

structure Context where
  births : List Ticket
  initialLedger : Ledger
  bindings : List Binding
  locals : List TxLocalBatch
  pid : PeerId

def Context.items (context : Context) : List SkbId := context.bindings.map Binding.skb

inductive Phase where
  | sending (remaining : List SkbId)
  | freeing (remaining : List SkbId)

def Phase.active (context : Context) : Phase → List SkbId
  | .sending _ => context.items
  | .freeing remaining => remaining

def Phase.remaining : Phase → List SkbId
  | .sending remaining => remaining
  | .freeing remaining => remaining

def Phase.assigned (context : Context) (phase : Phase) (ledger : Ledger)
    (debts : List CleanupDebt) : Prop :=
  ∀ binding ∈ context.bindings,
    match phase with
    | .sending remaining =>
      (binding.skb ∈ remaining → binding.pending ledger) ∧
      (binding.skb ∉ remaining → binding.debt ledger debts)
    | .freeing remaining =>
      binding.terminal ledger ∧ (binding.skb ∈ remaining → binding.debt ledger debts)

/-- The active batch remains a native caller local. Processed sends are
terminal debt, while unsent items remain pending. During free, only the exact
remaining suffix is resident caller ownership; terminal ledger entries remain. -/
def State (context : Context) (phase : Phase) (history : List CausalJournal.Event) (w : World) : Prop :=
  ∃ ledger debts,
    Staged.Obligations.Step context.initialLedger ledger ∧
    FirstTerminal.Support context.births history ledger debts w.wg ∧
    (∀ binding ∈ context.bindings, binding.recorded history) ∧
    phase.remaining.IsSuffix context.items ∧ phase.assigned context ledger debts ∧
    TxCoverage (⟨.selected,context.pid,phase.active context⟩ :: context.locals) w.wg ∧
    TxInventory (⟨.selected,context.pid,phase.active context⟩ :: context.locals) w.wg

inductive Site where
  | marker (pid : PeerId) (items : List SkbId)
  | traversal (pid : PeerId)
  | authenticated (pid : PeerId)
  | packet (skb : SkbId)
  | send (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
  | accounting (pid : PeerId) (packet : RunWitness DataPacket) (ret : Int)
  | dataSent (pid : PeerId)
  | fresh (pid : PeerId)
  | free (skb : SkbId)
  | keyRelease (key : KeypairId)
  | peerRelease (pid : PeerId)

def discard (action : PrefixM E α) : PrefixM E Unit := do
  _ ← action
  pure ()

def Site.action : Site → PrefixM CausalJournal.Event Unit
  | .marker pid items => CausalJournal.completionOps.completion pid items
  | .traversal pid => CausalJournal.completionOps.traversal pid
  | .authenticated pid => CausalJournal.completionOps.sent pid
  | .packet skb => discard (captureObserved (CausalJournal.completionOps.packet skb))
  | .send pid skb receipt => discard (CausalJournal.completionOps.send pid skb receipt)
  | .accounting pid receipt ret => discard (FirstTerminal.focused
      (CompletionFirstTerminal.afterSocket pid receipt ret))
  | .dataSent pid => CausalJournal.completionOps.dataSent pid
  | .fresh pid => CausalJournal.completionOps.fresh pid
  | .free skb => FirstTerminal.cleanupFree skb
  | .keyRelease key => (TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal).access (keypairPutPrefix (some key) false)
  | .peerRelease pid => (TxSource.observed CausalJournal.txEvent CausalJournal.txEvent?
      CausalJournal.Event.stagedDisposal).release (some pid)

/-- Conservatively retain every event that could change fixed obligations.
An inner result followed by a stopped accounting callback cannot disappear
behind a frontier chosen before that result. -/
def changesLedger : CausalJournal.Event → Bool
  | .scope _ | .armed _ | .queued _ => false
  | .old (.disposition _) => false
  | _ => true

structure Frontier (context : Context) (reason : Stop) (history : List CausalJournal.Event) where
  phase : Phase
  site : Site
  world : World
  before : List CausalJournal.Event
  owned : State context phase before world
  prefixHistory : before.IsPrefix history
  nativeFailure : runPrefix site.action world before = (.error reason,history)
  lastCut : history.filter changesLedger = before.filter changesLedger

def Stopped (context : Context) (reason : Stop) (history : List CausalJournal.Event) : Prop :=
  Nonempty (Frontier context reason history)

/-- A stopped frontier retains the same fixed ledger and concrete active
local at its actual failed callback entry. In particular, a prior terminal
entry cannot be changed or dropped at this cut. -/
theorem Frontier.support (frontier : Frontier context reason history) :
    ∃ ledger debts, Staged.Obligations.Step context.initialLedger ledger ∧
      FirstTerminal.Support context.births frontier.before ledger debts frontier.world.wg ∧
      TxCoverage (⟨.selected,context.pid,frontier.phase.active context⟩ :: context.locals) frontier.world.wg ∧
      TxInventory (⟨.selected,context.pid,frontier.phase.active context⟩ :: context.locals) frontier.world.wg := by
  obtain ⟨ledger,debts,step,support,_,_,_,coverage,inventory⟩ := frontier.owned
  exact ⟨ledger,debts,step,support,coverage,inventory⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
