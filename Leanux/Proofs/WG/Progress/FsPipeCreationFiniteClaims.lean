import Leanux.Proofs.WG.Progress.FsPipeDescriptorFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! Unrestricted campaign projections of exact native pipe-creation
equalities. Native equations retain full FS/task/Ambient outcomes. -/

theorem original_getPipeInode_finite :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.getPipeInode)) (liftFS (getPipeInode)) := by
  rw [getPipeInode_source]
  intro w pre
  rfl

theorem original_allocFileClone_finite (base : FileId) (flags : UInt32) (fopId : FopsId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.allocFileClone base flags fopId)) (liftFS (allocFileClone base flags fopId)) := by
  rw [allocFileClone_source]
  intro w pre
  rfl

theorem original_createPipeFiles_finite (flags : UInt32) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.createPipeFiles flags)) (liftFS (createPipeFiles flags)) := by
  rw [createPipeFiles_source]
  intro w pre
  rfl

theorem original_doPipeFlags_finite (flags : UInt32) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.doPipeFlags flags)) (liftFS (doPipeFlags flags)) := by
  rw [doPipeFlags_source]
  intro w pre
  rfl

theorem original_doPipe2_finite (flags : UInt32) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.doPipe2 flags)) (liftFS (doPipe2 flags)) := by
  rw [doPipe2_source]
  intro w pre
  rfl

theorem original_sysPipe2_finite (flags : UInt32) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.sysPipe2 flags)) (liftFS (sysPipe2 flags)) := by
  rw [sysPipe2_source]
  intro w pre
  rfl


end Leanux.Proofs.WG.Progress.FsFinite
