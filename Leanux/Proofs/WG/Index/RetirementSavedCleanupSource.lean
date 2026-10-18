import Leanux.Proofs.WG.Index.RetirementFirstPassSource
import Leanux.Proofs.WG.Index.RetirementBeforePaymentSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Leanux.Proofs.Framing
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

/-- The actual saved cleanup loop consumes the ordered stamped occurrences
one at a time. Its selected-send premise is needed only at genuine remaining
suffixes; equal owners are not collapsed and no extra account walk is added. -/
theorem saved_cleanup_retirement
    (original : DurableHolders) (cs : Ledger)
    (retired loans : Reservations) (saved : Reservations)
    (send : ∀ done paid tail, saved = done ++ paid :: tail →
      SelectedDrain.SendKeeps
        (RetirementWork original cs (paid :: ((tail ++ retired) ++ loans))
          (tail ++ retired)) runFlushedSendWork) :
    Ensures (for pid in saved.map Owner.slot do
        _ ← branch .peerRemoveAllIter2 true
        peerRemoveAfterDead pid : WG.M Unit)
      (RetirementWork original cs ((saved ++ retired) ++ loans) (saved ++ retired))
      (fun _ => RetirementWork original cs (retired ++ loans) retired) := by
  induction saved with
  | nil =>
    intro w a result v b hi run
    simp only [List.map_nil,List.forIn_nil] at run
    cases run
    simpa only [List.nil_append] using hi
  | cons paid tail ih =>
    have nextSend : ∀ done owner rest, tail = done ++ owner :: rest →
        SelectedDrain.SendKeeps
          (RetirementWork original cs (owner :: ((rest ++ retired) ++ loans))
            (rest ++ retired)) runFlushedSendWork := by
      intro done owner rest same
      apply send (paid :: done) owner rest
      simpa only [List.cons_append] using congrArg (List.cons paid) same
    have factor : (for pid in (paid :: tail).map Owner.slot do
        _ ← branch .peerRemoveAllIter2 true
        peerRemoveAfterDead pid : WG.M Unit) = (do
        _ ← branch .peerRemoveAllIter2 true
        peerRemoveAfterDead paid.slot
        for pid in tail.map Owner.slot do
          _ ← branch .peerRemoveAllIter2 true
          peerRemoveAfterDead pid) := by
      simp only [List.map_cons,List.forIn_cons,bind_assoc,pure_bind]
    rw [factor]
    refine ensures_bind _ _
      ((ensures_iff _ _ _).mpr (hoare_liftAmbient
        (AmbientM.branch .peerRemoveAllIter2 true) _)) ?_
    intro _
    refine ensures_bind _ _ ?_ (fun _ => ih nextSend)
    simpa only [List.cons_append] using peerRemoveAfterDead_retirement original cs paid
      (tail ++ retired) loans (send [] paid tail rfl)

/-- The exact remainder of original peerRemoveAll includes the first-pass
terminal branch, every saved cleanup, then the cleanup terminal branch.
Only a normal endpoint is claimed, under the suffix-local send contracts. -/
theorem retirementAfterFirstPass_retirement
    (original : DurableHolders) (cs : Ledger)
    (retired loans : Reservations) (saved : Reservations)
    (send : ∀ done paid tail, saved = done ++ paid :: tail →
      SelectedDrain.SendKeeps
        (RetirementWork original cs (paid :: ((tail ++ retired) ++ loans))
          (tail ++ retired)) runFlushedSendWork) :
    Ensures (retirementAfterFirstPass (saved.map Owner.slot))
      (RetirementWork original cs ((saved ++ retired) ++ loans) (saved ++ retired))
      (fun _ => RetirementWork original cs (retired ++ loans) retired) := by
  let loop : WG.M Unit := do
    for pid in saved.map Owner.slot do
      _ ← branch .peerRemoveAllIter2 true
      peerRemoveAfterDead pid
  have factor : retirementAfterFirstPass (saved.map Owner.slot) = (do
      _ ← branch .peerRemoveAllIter1 false
      loop
      _ ← branch .peerRemoveAllIter2 false
      pure ()) := by
    simp only [retirementAfterFirstPass,loop,bind_assoc,pure_bind]
  rw [factor]
  refine ensures_bind _ _
    ((ensures_iff _ _ _).mpr (hoare_liftAmbient
      (AmbientM.branch .peerRemoveAllIter1 false) _)) ?_
  intro _
  refine ensures_bind _ _ (saved_cleanup_retirement original cs retired loans saved send) ?_
  intro _
  refine ensures_bind _ _
    ((ensures_iff _ _ _).mpr (hoare_liftAmbient
      (AmbientM.branch .peerRemoveAllIter2 false) _)) ?_
  intro _ w a result v b hi run
  cases run
  exact hi

end Leanux.Proofs.WG.Index
