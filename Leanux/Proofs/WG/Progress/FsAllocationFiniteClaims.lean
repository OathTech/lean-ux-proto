import Leanux.Proofs.WG.Progress.FsAnonymousFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! The native equalities preserve the full FS/task/Ambient outcomes, including
allocation failures and Stops. These claims expose the existing campaign
product projection, which does not itself display every FS field. -/

theorem original_allocEmptyFile_finite (flags : UInt32) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.allocEmptyFile flags)) (liftFS (allocEmptyFile flags)) := by
  rw [allocEmptyFile_source]
  intro w pre
  rfl

theorem original_allocPathPseudo_finite (inode : InodeId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.allocPathPseudo inode)) (liftFS (allocPathPseudo inode)) := by
  rw [allocPathPseudo_source]
  intro w pre
  rfl

theorem original_allocFdtable_finite (slotsWanted : Nat) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.allocFdtable slotsWanted)) (liftFS (allocFdtable slotsWanted)) := by
  rw [allocFdtable_source]
  intro w pre
  rfl

theorem original_allocPipeInfo_finite :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.allocPipeInfo)) (liftFS (allocPipeInfo)) := by
  rw [allocPipeInfo_source]
  intro w pre
  rfl

theorem original_allocFile_finite (flags : UInt32) (fopId : FopsId) (inode : InodeId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.allocFile flags fopId inode)) (liftFS (allocFile flags fopId inode)) := by
  rw [allocFile_source]
  intro w pre
  rfl

theorem original_allocFilePseudo_finite (flags : UInt32) (inode : InodeId) (fopId : FopsId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.allocFilePseudo flags inode fopId)) (liftFS (allocFilePseudo flags inode fopId)) := by
  rw [allocFilePseudo_source]
  intro w pre
  rfl

theorem original_anonInodeGetfileImpl_finite (fopId : FopsId) (priv : PrivateData) (flags : UInt32) (makeInode : Bool) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.anonInodeGetfileImpl fopId priv flags makeInode)) (liftFS (anonInodeGetfileImpl fopId priv flags makeInode)) := by
  rw [anonInodeGetfileImpl_source]
  intro w pre
  rfl

theorem original_anonInodeGetfile_finite (fopId : FopsId) (priv : PrivateData) (flags : UInt32) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.anonInodeGetfile fopId priv flags)) (liftFS (anonInodeGetfile fopId priv flags)) := by
  rw [anonInodeGetfile_source]
  intro w pre
  rfl

end Leanux.Proofs.WG.Progress.FsFinite
