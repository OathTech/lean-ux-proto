import Leanux.Proofs.WG.Progress.FsReadWriteFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! Exact native equations preserve all FS fields; these claims expose the
campaign product projection and every original Stop. -/

theorem original_newSyncRead_finite (fid : FileId) (len : Nat) (ppos : Option Int) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.newSyncRead fid len ppos)) (liftFS (newSyncRead fid len ppos)) := by
  rw [newSyncRead_source]
  intro w pre
  rfl

theorem original_vfsRead_finite (fid : FileId) (count : Nat) (pos : Option Int) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.vfsRead fid count pos)) (liftFS (vfsRead fid count pos)) := by
  rw [vfsRead_source]
  intro w pre
  rfl

theorem original_ksysRead_finite (fd : Nat) (count : Nat) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.ksysRead fd count)) (liftFS (ksysRead fd count)) := by
  rw [ksysRead_source]
  intro w pre
  rfl

theorem original_newSyncWrite_finite (fid : FileId) (buf : ByteArray) (len : Nat) (ppos : Option Int) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.newSyncWrite fid buf len ppos)) (liftFS (newSyncWrite fid buf len ppos)) := by
  rw [newSyncWrite_source]
  intro w pre
  rfl

theorem original_vfsWrite_finite (fid : FileId) (buf : ByteArray) (count : Nat) (pos : Option Int) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.vfsWrite fid buf count pos)) (liftFS (vfsWrite fid buf count pos)) := by
  rw [vfsWrite_source]
  intro w pre
  rfl

theorem original_ksysWrite_finite (fd : Nat) (buf : ByteArray) (count : Nat) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.ksysWrite fd buf count)) (liftFS (ksysWrite fd buf count)) := by
  rw [ksysWrite_source]
  intro w pre
  rfl

end Leanux.Proofs.WG.Progress.FsFinite
