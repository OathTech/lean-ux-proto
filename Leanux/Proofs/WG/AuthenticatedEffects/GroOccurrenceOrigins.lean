import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePollChecked
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeProduct

/-! Positional stack-origin evidence is independent of authentication and of
scope metadata alone. A stack scope is checked against its own retained GRO
occurrence, and its native replay receipt can then be authenticated in the
same complete journal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged
variable {E : Type}

def Checked (candidate : Nat → SkbId → RxPacket → E) (record : TransportDriver.Replay → E)
    (stack : E → Option Entry) (before : List E) (event : E) : Prop :=
  ∀ entry, stack event = some entry → Accepted candidate record entry before

def Safe (candidate : Nat → SkbId → RxPacket → E) (record : TransportDriver.Replay → E)
    (stack : E → Option Entry) (history : List E) : Prop :=
  ∀ before event after, history = before ++ event :: after → Checked candidate record stack before event

theorem Safe.empty (candidate : Nat → SkbId → RxPacket → E) (record : TransportDriver.Replay → E)
    (stack : E → Option Entry) : Safe candidate record stack [] := by
  intro before event after position
  have lengths := congrArg List.length position
  simp at lengths

theorem Safe.append {candidate : Nat → SkbId → RxPacket → E} {record : TransportDriver.Replay → E}
    {stack : E → Option Entry} {history suffix : List E} (safe : Safe candidate record stack history)
    (next : ∀ before event after, suffix = before ++ event :: after →
      Checked candidate record stack (history ++ before) event) :
    Safe candidate record stack (history ++ suffix) := by
  unfold Safe at *
  exact (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    (Checked candidate record stack) history suffix safe next

theorem Safe.quiet {candidate : Nat → SkbId → RxPacket → E} {record : TransportDriver.Replay → E}
    {stack : E → Option Entry} {history suffix : List E} (safe : Safe candidate record stack history)
    (quiet : ∀ event ∈ suffix, stack event = none) : Safe candidate record stack (history ++ suffix) := by
  apply safe.append
  intro before event after position entry found
  have member : event ∈ suffix := by rw [position]; simp
  rw [quiet event member] at found
  cases found

theorem Safe.entry {candidate : Nat → SkbId → RxPacket → E} {record : TransportDriver.Replay → E}
    {stack : E → Option Entry} {history : List E} (safe : Safe candidate record stack history)
    (event : E) (entry : Entry) (decode : stack event = some entry)
    (accepted : Accepted candidate record entry history) :
    Safe candidate record stack (history ++ [event]) := by
  apply safe.append
  intro before value after position other found
  cases before with
  | nil =>
    cases position
    have equal : entry = other := Option.some.inj (decode.symm.trans found)
    simpa only [List.append_nil,← equal] using accepted
  | cons first rest =>
    have lengths := congrArg List.length position
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega

theorem scope_checked
    (candidate : Nat → SkbId → RxPacket → E) (replay : TransportDriver.Replay → E)
    (stack : E → Option Entry) (record : CausalScope.Event Cause → E) (cause : Entry → Cause)
    (entered : ∀ position entry, stack (record (.entered ⟨position,cause entry⟩)) = some entry)
    (exited : ∀ position, stack (record (.exited position)) = none)
    (entry : Entry) (body : PrefixM E Unit)
    (checked : PrefixPreserves (fun h (_ : World) => Safe candidate replay stack h)
      (Safe candidate replay stack) body) :
    PrefixEnsures (fun h (_ : World) => Safe candidate replay stack h ∧ Accepted candidate replay entry h)
      (Safe candidate replay stack) (CausalScope.prefixScope record (cause entry) (fun _ => body))
      (fun _ h _ => Safe candidate replay stack h) := by
  intro w h input
  let marker := record (.entered ⟨h.length,cause entry⟩)
  have openSafe : Safe candidate replay stack (h ++ [marker]) :=
    input.1.entry marker entry (entered h.length entry) input.2
  obtain ⟨suffix,grown,safe,_⟩ := checked w (h ++ [marker]) openSafe
  rw [CausalScope.prefix_run]
  cases run : runPrefix body w (h ++ [marker]) with
  | mk result history =>
    rw [run] at grown safe
    dsimp only at grown safe
    cases result with
    | error stop =>
      exact ⟨marker :: suffix,by simpa only [List.append_assoc,List.singleton_append] using grown,safe,True.intro⟩
    | ok output =>
      have final := safe.quiet (suffix := [record (.exited h.length)]) (by
        intro event member
        obtain rfl := List.mem_singleton.mp member
        exact exited h.length)
      refine ⟨marker :: (suffix ++ [record (.exited h.length)]),?_,final,final⟩
      simp only [grown,List.append_assoc,List.cons_append,List.nil_append]

theorem stack_checked (candidate : Nat → SkbId → RxPacket → E) (replay : TransportDriver.Replay → E)
    (stack : E → Option Entry)
    (scope : Entry → PrefixM E Unit → PrefixM E Unit)
    (callback : List UInt8 → PrefixM E Unit)
    (checked : ∀ entry, PrefixEnsures
      (fun h (_ : World) => Safe candidate replay stack h ∧ Accepted candidate replay entry h)
      (Safe candidate replay stack) (scope entry (callback entry.bytes))
      (fun _ h _ => Safe candidate replay stack h)) (entries : List Entry) :
    PrefixEnsures (fun h (_ : World) => Safe candidate replay stack h ∧
      ∀ entry ∈ entries, Accepted candidate replay entry h)
      (Safe candidate replay stack) (stackWith scope callback entries)
      (fun _ h _ => Safe candidate replay stack h) := by
  induction entries with
  | nil => exact PrefixEnsures.pure (fun _ _ input => input.1) (fun _ _ input => input.1)
  | cons entry entries ih =>
    simp only [stackWith,List.forM_eq_forM,List.forM_cons] at *
    apply PrefixEnsures.bind _ (fun _ => ih)
    apply (remember _ (checked entry) (fun h => ∀ value ∈ entries, Accepted candidate replay value h)
      (fun history suffix input value member => accepted_monotone candidate replay value history suffix (input value member))).consequence
    · intro _ _ input
      exact ⟨⟨input.1,input.2 entry (by simp)⟩,fun value member => input.2 value (by simp [member])⟩
    · intro _ _ _ output; exact output

end Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence.Origins
