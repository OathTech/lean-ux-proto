import Leanux.Proofs.WG.HandshakeSecurity.StagingOwnerFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialState

/-! The actual selection observer retains current-slot compatibility until
staging checks the selected key's owner. No endpoint-erasure history join is
used: this contract runs the same selection callback in the TX journal. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder

theorem owner_selection (pid : PeerId) :
    StatePrefixEnsures (With CurrentSlots.Inv) Safe (Journal.selection pid)
      (fun x => With (OwnerSelected pid x)) := by
  apply state_quiet_extra (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other _ _ _ (fun _ => rfl) ((DriverCuts.selection pid).run w))
    (focusStatePrefix_erases _ _ (DriverCuts.selection_erases pid))
  intro h
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (NativeFrames.selection pid) w a x v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp (selection_owner pid) w a x v b hi.2 run⟩

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
