import Leanux.Proofs.WG.Index.RetirementWorkFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Leanux.Proofs.Framing Leanux.Proofs.Logged
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

/-- Reuse the exact original pre-payment cut. This definition deliberately
pins the private C1 HolderRetirement.beforePayment API rather than copying its
source body; its factor theorem is reused below. -/
def retirementBeforePayment (pid : PeerId) : WG.M Unit :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderRetirement.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.beforePayment) pid

theorem peerRemoveAfterDead_retirement_factor (pid : PeerId) :
    peerRemoveAfterDead pid = (do retirementBeforePayment pid; peerPut (some pid)) := by
  unfold retirementBeforePayment
  exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderRetirement.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.afterDead_factor) pid

theorem flushedClear_retirementWork
    (original : DurableHolders) (cs : Ledger) (loans retired : Reservations) :
    SelectedDrain.ClearKeeps (RetirementWork original cs loans retired) runFlushedClearWork := by
  intro w v d pid a b hi device member run
  have account := (pinned_const _private.Leanux.Proofs.WG.Queues.HolderDrains.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.clear_selected)
    hi.account device member a b run
  have configured := (hoare_iff_run_ambient _ _ _).mp (ConfiguredRemoval.flushedClear pid)
    w a () v b hi.configured run
  have base := BaseCoherence.transport hi.base
    ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.flushedClear_view pid)
      w a () v b run)
  have safety := runFlushedClearWork_hashSlots_coherent pid
    w a () v b ⟨hi.covered,hi.coherent⟩ run
  have reserved := runFlushedClearWork_retirement retired pid
    w a () v b hi.reserved run
  exact ⟨account,configured,base,safety.1,safety.2,reserved⟩

theorem drain_retirementWork
    (original : DurableHolders) (cs : Ledger) (loans retired : Reservations)
    (send : SelectedDrain.SendKeeps (RetirementWork original cs loans retired) runFlushedSendWork)
    (upTo : Option PeerId) :
    Preserves (RetirementWork original cs loans retired) (drainHandshakeSendWq upTo) :=
  SelectedDrain.original_preserves _ send (flushedClear_retirementWork original cs loans retired) upTo

theorem timersStop_retirementWork (original : DurableHolders) (cs : Ledger)
    (loans retired : Reservations)
    (send : SelectedDrain.SendKeeps (RetirementWork original cs loans retired) runFlushedSendWork)
    (pid : PeerId) :
    Preserves (RetirementWork original cs loans retired) (timersStop pid) :=
  (ensures_iff _ _ _).mp (Index.timersStop_preserves _
    (fun pid timer => (ensures_iff _ _ _).mpr
      (delTimer_retirementWork original cs loans retired pid timer))
    (fun upTo => (ensures_iff _ _ _).mpr
      (drain_retirementWork original cs loans retired send upTo)) pid)

/-- The real clear operation removes the paid retirement occurrence only after
its key slots have been cleared; the funded account still contains that loan. -/
theorem keypairsClear_retirementWork (original : DurableHolders) (cs : Ledger)
    (loans retired : Reservations) (paid : Owner) :
    Ensures (keypairsClear paid.slot)
      (RetirementWork original cs loans (paid :: retired))
      (fun _ => RetirementWork original cs loans retired) := by
  intro w a result v b hi run
  cases result
  have account := (hoare_iff_run_ambient _ _ _).mp
    (DurableHolders.keypairsClear_preserves paid.slot) w a () v b hi.account run
  have configured := (hoare_iff_run_ambient _ _ _).mp
    (ConfiguredRemoval.frame (ConfiguredMaintenance.keypairsClear_view paid.slot))
      w a () v b hi.configured run
  have base := BaseCoherence.transport hi.base
    ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.keypairsClear_view paid.slot)
      w a () v b run)
  have safety := keypairsClear_retirement_discharge paid retired
    w a () v b ⟨hi.covered,hi.coherent,hi.reserved⟩ run
  exact ⟨account,configured,base,safety.1,safety.2.1,safety.2.2⟩

/-- The original prefix's single clear moves from the head retirement list to
its tail. Timer deletion, both real drains, guards and scalar accounting then
retain that tail while the paid loan remains funded until the final put. -/
theorem retirementBeforePayment_transition
    (original : DurableHolders) (cs : Ledger) (paid : Owner)
    (retired loans : Reservations)
    (send : SelectedDrain.SendKeeps
      (RetirementWork original cs (paid :: (retired ++ loans)) retired) runFlushedSendWork) :
    Ensures (retirementBeforePayment paid.slot)
      (RetirementWork original cs (paid :: (retired ++ loans)) (paid :: retired))
      (fun _ => RetirementWork original cs (paid :: (retired ++ loans)) retired) := by
  let Before := RetirementWork original cs (paid :: (retired ++ loans)) (paid :: retired)
  let After := RetirementWork original cs (paid :: (retired ++ loans)) retired
  have ambient (P : WGWorld → Prop) {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient action P)
  have pureValue (P : WGWorld → Prop) {α : Type} (value : α) :
      Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro w a result v b hi run
    cases run
    exact hi
  have peer : Ensures (getPeer paid.slot) Before (fun _ => Before) := by
    intro w a p v b hi run
    exact (Queues.getPeer_normal paid.slot w v p a b run).1 ▸ hi
  have dev : Ensures getDev After (fun _ => After) := by
    intro w a d v b hi run
    exact (DecryptCarrier.getDev_current a b run).1 ▸ hi
  change Ensures (getPeer paid.slot >>= _) Before (fun _ => After)
  refine ensures_bind _ _ peer ?_
  intro p
  refine ensures_bind _ _ (ambient Before (AmbientM.branch .peerRemoveNotDead (!p.isDead))) ?_
  intro notDead
  refine ensures_bind (Q := fun _ => Before) _ _ ?_ ?_
  · split
    · exact ambient Before (AmbientM.unsupported _)
    · exact pureValue Before ()
  · intro _
    refine ensures_bind _ _ (keypairsClear_retirementWork original cs
      (paid :: (retired ++ loans)) retired paid) ?_
    intro _
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (timersStop_retirementWork original cs (paid :: (retired ++ loans)) retired send paid.slot)) ?_
    intro _
    refine ensures_bind _ _ dev ?_
    intro d
    refine ensures_bind (Q := fun _ => After) _ _ ?_ ?_
    · split
      · exact ambient After (AmbientM.unsupported _)
      · exact pureValue After ()
    · intro _
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
        (drain_retirementWork original cs (paid :: (retired ++ loans)) retired send none)) ?_
      intro _
      refine ensures_bind _ _ dev ?_
      intro d
      refine ensures_bind (Q := fun _ => After) _ _ ?_ ?_
      · split
        · exact ambient After (AmbientM.invariant _)
        · exact pureValue After ()
      · intro _
        exact (ensures_iff _ _ _).mpr
          (decrement_retirementWork original cs (paid :: (retired ++ loans)) retired)

/-- The actual after-dead operation discharges its paid retirement occurrence,
executes its original flushes and guards, then pays exactly that funded loan.
The only remaining callback obligation is the selected actual send-work path.
No completion, initialized-state, or unselected sender premise is asserted. -/
theorem peerRemoveAfterDead_retirement
    (original : DurableHolders) (cs : Ledger) (paid : Owner)
    (retired loans : Reservations)
    (send : SelectedDrain.SendKeeps
      (RetirementWork original cs (paid :: (retired ++ loans)) retired) runFlushedSendWork) :
    Ensures (peerRemoveAfterDead paid.slot)
      (RetirementWork original cs (paid :: (retired ++ loans)) (paid :: retired))
      (fun _ => RetirementWork original cs (retired ++ loans) retired) := by
  rw [peerRemoveAfterDead_retirement_factor]
  refine ensures_bind _ _
    (retirementBeforePayment_transition original cs paid retired loans send) ?_
  intro _ w a result v b hi run
  cases result
  have payment := peerPut_retirement_payment original cs paid retired loans
    w v a b hi.configured hi.base hi.account hi.covered hi.coherent hi.reserved run
  have configured := (hoare_iff_run_ambient _ _ _).mp
    (ConfiguredIdentity.peerPut_preserves (some paid.slot))
      w a () v b hi.configured run
  have base := BaseCoherence.transport hi.base
    ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.peerPut_view (some paid.slot))
      w a () v b run)
  exact ⟨payment.1,configured,base,payment.2.1,payment.2.2.1,payment.2.2.2⟩

end Leanux.Proofs.WG.Index
