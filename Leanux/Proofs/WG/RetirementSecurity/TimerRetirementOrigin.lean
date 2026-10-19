import Leanux.Proofs.WG.RetirementSecurity.ConditionalRetirement
import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionInitialized

/-! The final initialized causal journal selects the exact pending zero-key
timer occurrence installed by an earlier actual native arm. This provenance
fact is separate from the explicit worker-progress retirement contracts. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TimerRetirementOrigin
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects

theorem initialized (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (receipt : TimerDispatch.Selection)
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2=
      pre++CausalJournal.Event.old (.timerSelected receipt)::post)
    (zero : receipt.timer=.zeroKeyMaterial) :
    receipt.Valid ∧ ∃ before after arm stamp expires,
      pre=before++CausalJournal.Event.armed arm::after ∧ arm.Valid ∧ TimerOccurrences.Changed arm ∧
      arm.peer=receipt.peer ∧ arm.timer=.zeroKeyMaterial ∧
      TimerSlots.Pending arm.run.after receipt.peer .zeroKeyMaterial stamp expires receipt.entry ∧
      TimerSlots.Pending receipt.before.wg receipt.peer .zeroKeyMaterial stamp expires receipt.entry := by
  obtain ⟨valid,before,after,arm,stamp,expires,found,native,changed,peer,timer,armed,pending⟩ :=
    CausalJournal.Selections.initialized_timer_arm trace placeholders pre post receipt position
  exact ⟨valid,before,after,arm,stamp,expires,found,native,changed,peer,timer.trans zero,
    by simpa only [zero] using armed,by simpa only [zero] using pending⟩

end Leanux.Proofs.WG.RetirementSecurity.TimerRetirementOrigin
