import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionFrontObserved
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationTrimTotal

/-! Public local outcomes for the complete enriched front. Every normal
result has a canonical fixed ledger; a stopped run exposes its last accounted
native cut, rather than asserting a nonexistent failed post-state. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal
set_option pp.structureInstances false

theorem normal_result (entry : Entry) (input : Input)
    (canonical : entry.births = Staged.Obligations.births entry.history)
    (a b : Ambient) (v : WGWorld) (history : List Event) (value : Except Int PeerId)
    (run : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu)
      entry.world a entry.history = (.ok ((value,v),b),history)) :
    Result (entry.withInput input) input value history v b := by
  obtain ⟨_,_,_,normal⟩ := front_checked entry input canonical
    entry.world a entry.history ⟨rfl,rfl⟩
  change runPrefix
    ((CausalJournal.front input.family input.address input.packets input.mtu).run entry.world)
    a entry.history = _ at run
  rw [run] at normal
  exact normal

/-- The whole normal front accounts for every canonical admission in this
history and retains every prior terminal record. The incoming ledger is explicit. -/
theorem normal_conservation (entry : Entry) (input : Input)
    (canonical : entry.births = Staged.Obligations.births entry.history)
    (a b : Ambient) (v : WGWorld) (history : List Event) (value : Except Int PeerId)
    (run : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu)
      entry.world a entry.history = (.ok ((value,v),b),history)) :
    ∃ ledger, Valid (Staged.Obligations.births history) ledger ∧ QueueInv history ledger v ∧
      ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ entry.ledger →
        (ticket,Status.terminal outcome) ∈ ledger := by
  obtain ⟨priorHistory,r,ledger,position,_,_,after,_,normal⟩ :=
    normal_result entry input canonical a b v history value run
  refine ⟨ledger,?_,?_,normal.2.2.2.1⟩
  · rw [position]; exact normal.2.1
  · rw [position,←after]; exact normal.2.2.1

/-- The native check, lookup, selection and splice equations are connected
and derived from this actual successful callback, not caller assumptions. -/
theorem accepted_native_cut (entry : Entry) (input : Input)
    (a b : Ambient) (v : WGWorld) (history : List Event) (pid : PeerId)
    (run : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu)
      entry.world a entry.history = (.ok ((.ok pid,v),b),history)) :
    Packets.TxFrontCut input.family input.address input.packets input.mtu entry.world v a b pid := by
  have native := HandshakeSecurity.StagedConservation.Front.observed_erases
    Event.transmitInput Event.stagedDisposal stagedDisposal? routedEvent
    input entry.world a entry.history
  change (runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu)
    entry.world a entry.history).1 = _ at native
  rw [run] at native
  exact Packets.txFront_cut _ _ _ _ _ _ _ _ _ native.symm

/-- A stopped front retains a canonical ledger at its actual entry or last
completed disposal receipt. No failed World is invented by this claim. -/
theorem stopped_conservation (entry : Entry) (input : Input)
    (canonical : entry.births = Staged.Obligations.births entry.history)
    (a : Ambient) (history : List Event) (stop : Stop)
    (run : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu)
      entry.world a entry.history = (.error stop,history)) :
    ∃ ledger snapshot, Checkpoint (entry.withInput input) history ledger snapshot ∧
      Valid (Staged.Obligations.births history) ledger ∧ QueueInv history ledger snapshot ∧
      ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ entry.ledger →
        (ticket,Status.terminal outcome) ∈ ledger := by
  let initial := entry.withInput input
  obtain ⟨_,_,safe,_⟩ := body_checked (entry := initial)
    input.family input.address input.packets input.mtu entry.world a initial.history ⟨rfl,initial.queues⟩
  rw [front_run] at run
  cases executed : runWGPrefix (body input.family input.address input.packets input.mtu)
      entry.world a initial.history with
  | mk result hist =>
    change runPrefix ((body input.family input.address input.packets input.mtu).run entry.world)
      a initial.history = _ at executed
    rw [executed] at safe
    change runWGPrefix (body input.family input.address input.packets input.mtu)
      entry.world a (entry.history ++ [.transmitInput input]) = _ at executed
    rw [executed] at run
    cases result with
    | ok out => cases run
    | error err =>
      have same : hist = history := congrArg Prod.snd run
      subst hist
      obtain ⟨ledger,snapshot,cut,valid,queues,retained⟩ := safe.retains
      have domain := cut.canonical (entry.withInput_canonical input canonical)
      exact ⟨ledger,snapshot,cut,domain ▸ valid,queues,retained⟩

/-- The overflow callback cannot hide a partially counted native trim: any
Stop is its first peer read, before the queue or drop counter can be changed. -/
theorem trim_stopped_before_disposal (pid : PeerId) (w : WGWorld) (a : Ambient)
    (h history : List Event) (stop : Stop)
    (run : runWGPrefix (ops.trim pid) w a h = (.error stop,history)) :
    history = h ∧ ((getPeer pid).run w).run a = .error stop := by
  rw [trim_run] at run
  cases native : ((Lifetimes.xmitTrim pid).run w).run a with
  | error err =>
    simp only [native,Prod.mk.injEq,Except.error.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    exact ⟨rfl,HandshakeSecurity.StagedConservation.Trim.stopped_first pid w a _ native⟩
  | ok out => simp only [native] at run; cases run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front
