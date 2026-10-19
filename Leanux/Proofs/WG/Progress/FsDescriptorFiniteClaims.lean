import Leanux.Proofs.WG.Progress.FsEventfdFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! Native equalities retain the full FS, task and Ambient result. These
claims expose the existing campaign product projection, including Stops. -/

theorem original_expandFdtable_finite (nr : Nat) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.expandFdtable nr)) (liftFS (expandFdtable nr)) := by
  rw [expandFdtable_source]
  intro w pre
  rfl

theorem original_expandFiles_finite (nr : Nat) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.expandFiles nr)) (liftFS (expandFiles nr)) := by
  rw [expandFiles_source]
  intro w pre
  rfl

theorem original_allocFd_finite (start «end» : Nat) (flags : UInt32) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.allocFd start «end» flags)) (liftFS (allocFd start «end» flags)) := by
  rw [allocFd_source]
  intro w pre
  rfl

theorem original_getUnusedFdFlags_finite (flags : UInt32) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.getUnusedFdFlags flags)) (liftFS (getUnusedFdFlags flags)) := by
  rw [getUnusedFdFlags_source]
  intro w pre
  rfl

theorem original_doEventfd_finite (count flags : UInt32) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.doEventfd count flags)) (liftFS (doEventfd count flags)) := by
  rw [doEventfd_source]
  intro w pre
  rfl

theorem original_sysEventfd2_finite (count flags : UInt32) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.sysEventfd2 count flags)) (liftFS (sysEventfd2 count flags)) := by
  rw [sysEventfd2_source]
  intro w pre
  rfl


end Leanux.Proofs.WG.Progress.FsFinite
