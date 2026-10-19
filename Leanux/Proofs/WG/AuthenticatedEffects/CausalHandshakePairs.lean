import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalSource
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeScopePrefix
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsHistory

/-! Each handshake scope is followed immediately by its own callback marker.
The relation uses full-journal positions; an unrelated older callback cannot
satisfy it. It does not by itself authenticate the callback. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.HandshakePairs
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

def required : Event → Option Event
  | .scope (.entered ⟨_,.handshake kind pid⟩) => some (.old (.handshake (.callback kind pid)))
  | _ => none

def Safe : List Event → Prop
  | [] => True
  | event :: rest => (∀ next, required event = some next → rest.head? = some next) ∧ Safe rest

def Quiet (event : Event) : Prop := required event = none

theorem Safe.append {history suffix : List Event} (left : Safe history) (right : Safe suffix) :
    Safe (history ++ suffix) := by
  induction history with
  | nil => exact right
  | cons event rest ih =>
    refine ⟨?_,ih left.2⟩
    intro next needed
    have found := left.1 next needed
    cases rest with
    | nil => cases found
    | cons first tail => exact found

theorem Safe.quiet {history suffix : List Event} (safe : Safe history)
    (quiet : ∀ event ∈ suffix, Quiet event) : Safe (history ++ suffix) := by
  apply safe.append
  induction suffix with
  | nil => trivial
  | cons event rest ih =>
    refine ⟨?_,ih (fun value member => quiet value (List.mem_cons_of_mem _ member))⟩
    intro next needed
    rw [quiet event (by simp)] at needed
    cases needed

theorem Safe.emit {history : List Event} (safe : Safe history) (event : Event) (quiet : Quiet event) :
    Safe (history ++ [event]) := safe.quiet (by
  intro value member
  obtain rfl := List.mem_singleton.mp member
  exact quiet)

theorem Safe.pair {history : List Event} (safe : Safe history) (index : Nat)
    (kind : HandshakeCausal.Kind) (pid : PeerId) :
    Safe (history ++ [.scope (.entered ⟨index,.handshake kind pid⟩),.old (.handshake (.callback kind pid))]) := by
  apply safe.append
  constructor
  · intro next needed; cases needed; rfl
  · constructor
    · intro next needed; cases needed
    · trivial

theorem Safe.next {history : List Event} (safe : Safe history)
    (before after : List Event) (index : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (position : history = before ++ .scope (.entered ⟨index,.handshake kind pid⟩) :: after) :
    ∃ rest, after = .old (.handshake (.callback kind pid)) :: rest := by
  rw [position] at safe
  clear position
  have tail : Safe (.scope (.entered ⟨index,.handshake kind pid⟩) :: after) := by
    induction before with
    | nil => exact safe
    | cons first rest ih => exact ih safe.2
  have found := tail.1 _ rfl
  cases after with
  | nil => cases found
  | cons event rest =>
    have same : event = .old (.handshake (.callback kind pid)) := Option.some.inj found
    exact ⟨rest,by rw [same]⟩

theorem emit_quiet (event : Event) (quiet : Quiet event) :
    Driver.StateHistorySafe Safe (emitStatePrefix event) :=
  StatePrefixEnsures.emit event (fun _ _ _ hi => hi.emit event quiet)
    (fun _ _ _ hi => hi.emit event quiet)

theorem receipt_quiet (body : WGPrefix Event α) (preserves : Driver.StateHistorySafe Safe body)
    (record : WGRunWitness α → Event) (quiet : ∀ r, Quiet (record r)) :
    Driver.StateHistorySafe Safe (receiptWGObserved body record) := by
  unfold receiptWGObserved
  exact Driver.History.state_bind preserves.captureWGObserved (fun r =>
    Driver.History.state_bind (emit_quiet (record r) (quiet r)) (fun _ => Driver.History.state_pure _))

/-- The source emits the entry and matching callback as one prefix before it
can encounter a stopping operation in the callback body. -/
theorem scoped_callback (kind : HandshakeCausal.Kind) (pid : PeerId)
    (body : WGPrefix Event α) (preserves : Driver.StateHistorySafe Safe body) :
    Driver.StateHistorySafe Safe
      (CausalScope.scope Event.scope (.handshake kind pid)
        (HandshakeWorker.callback (Event.old ∘ Journal.Event.handshake) kind pid body)) := by
  intro w a h hi
  let entryHistory := h ++ [.scope (.entered ⟨h.length,.handshake kind pid⟩),.old (.handshake (.callback kind pid))]
  obtain ⟨suffix,appends,safe,post⟩ := preserves w a entryHistory (hi.pair h.length kind pid)
  change (runWGPrefix body w a entryHistory).2 = entryHistory ++ suffix at appends
  change Safe (runWGPrefix body w a entryHistory).2 at safe
  clear post
  have equation := HandshakeEffects.callback_scope_run Event.scope (.handshake kind pid)
    (Event.old ∘ Journal.Event.handshake) kind pid body w a h
  change runPrefix (StateT.run (CausalScope.scope Event.scope (.handshake kind pid)
    (HandshakeWorker.callback (Event.old ∘ Journal.Event.handshake) kind pid body)) w) a h = _ at equation
  simp only [Function.comp_apply] at equation
  cases run : runWGPrefix body w a entryHistory with
  | mk result history =>
    rw [run] at appends safe
    change history = entryHistory ++ suffix at appends
    dsimp only [entryHistory] at run
    rw [run] at equation
    rw [equation]
    cases result with
    | error stop =>
      exact ⟨[.scope (.entered ⟨h.length,.handshake kind pid⟩),.old (.handshake (.callback kind pid))] ++ suffix,
        by simpa only [entryHistory,List.append_assoc] using appends,safe,True.intro⟩
    | ok result =>
      have closed := safe.emit (.scope (.exited h.length)) rfl
      exact ⟨[.scope (.entered ⟨h.length,.handshake kind pid⟩),.old (.handshake (.callback kind pid))] ++ suffix ++ [.scope (.exited h.length)],
        by simp only [appends,entryHistory,List.append_assoc],closed,closed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.HandshakePairs
