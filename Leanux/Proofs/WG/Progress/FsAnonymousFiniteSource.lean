import Leanux.Proofs.WG.Progress.FsAllocationFiniteSource
import Leanux.FS.AnonInodes

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! Native file creation using the finite allocation leaves. Error cleanup
and anonymous-inode refusal branches remain in their original order. -/

def allocFile (flags : UInt32) (fopId : FopsId) (inode : InodeId) : FS.M (Except Int FileId) := do
  let r ← allocEmptyFile flags
  if ← branch .allocFileOk (r matches .ok _) then
    if let .ok fid := r then fileInitPath fid fopId inode
  return r

theorem allocFile_source (flags : UInt32) (fopId : FopsId) (inode : InodeId) :
    Leanux.allocFile flags fopId inode = allocFile flags fopId inode := by
  unfold Leanux.allocFile allocFile
  simp only [allocEmptyFile_source]
  rfl

def allocFilePseudo (flags : UInt32) (inode : InodeId) (fopId : FopsId) : FS.M (Except Int FileId) := do
  let ret ← allocPathPseudo inode
  if ← branch .allocFilePseudoPathErr (ret != 0) then return .error ret
  let r ← allocFile flags fopId inode
  if ← branch .allocFilePseudoErr (r matches .error _) then
    if let .pipefs id := inode then
      setInode id { (← getInode id) with dCount := 0 }
  return r

theorem allocFilePseudo_source (flags : UInt32) (inode : InodeId) (fopId : FopsId) :
    Leanux.allocFilePseudo flags inode fopId = allocFilePseudo flags inode fopId := by
  unfold Leanux.allocFilePseudo allocFilePseudo
  simp only [allocPathPseudo_source, allocFile_source]
  rfl

def anonInodeGetfileImpl (fopId : FopsId) (priv : PrivateData) (flags : UInt32) (makeInode : Bool) :
    FS.M (Except Int FileId) := do
  let fop ← fopsOf (some fopId)
  if ← branch .anonGetfileOwner fop.owner then
    unsupported "try_module_get(fops->owner)"
  if ← branch .anonMakeInode makeInode then
    unsupported "anon_inode_make_secure_inode"
  -- inode = anon_inode_inode, set at boot by anon_inode_init
  if ← branch .anonInodeErr (← get).anonInodeInodeErr then return .error (-19)  -- -ENODEV
  -- ihold(inode)
  let file ← allocFilePseudo (flags &&& (O_ACCMODE ||| O_NONBLOCK)) .anon fopId
  if ← branch .anonGetfileFileErr (file matches .error _) then
    iputReport false  -- err_iput: iput(inode), the shared inode keeps its pinned reference
    return file       -- err: module_put(fops->owner)
  -- file->f_mapping = inode->i_mapping
  if let .ok fid := file then
    setFile fid { (← getFile fid) with privateData := some priv }  -- file->private_data = priv
  return file

theorem anonInodeGetfileImpl_source (fopId : FopsId) (priv : PrivateData) (flags : UInt32) (makeInode : Bool) :
    Leanux.anonInodeGetfileImpl fopId priv flags makeInode = anonInodeGetfileImpl fopId priv flags makeInode := by
  unfold Leanux.anonInodeGetfileImpl anonInodeGetfileImpl
  simp only [allocFilePseudo_source]
  rfl

def anonInodeGetfile (fopId : FopsId) (priv : PrivateData) (flags : UInt32) : FS.M (Except Int FileId) :=
  anonInodeGetfileImpl fopId priv flags false

theorem anonInodeGetfile_source (fopId : FopsId) (priv : PrivateData) (flags : UInt32) :
    Leanux.anonInodeGetfile fopId priv flags = anonInodeGetfile fopId priv flags := by
  unfold Leanux.anonInodeGetfile anonInodeGetfile
  simp only [anonInodeGetfileImpl_source]

end Leanux.Proofs.WG.Progress.FsFinite
