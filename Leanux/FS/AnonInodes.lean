import Leanux.FS.FileTable

/-!
# fs/anon_inodes.c — `anon_inode_getfile`

The shared anonymous inode (`anon_inode_inode`), `ihold`/`iput`,
`module_put` and `f_mapping` are cut points.
-/

namespace Leanux

/-- __anon_inode_getfile (anon_inodes.c:90-138). With `CONFIG_MODULES=n`,
    `try_module_get` is the constant `true`, so the owner test folds away. -/
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

/-- anon_inode_getfile (anon_inodes.c:156-161). -/
def anonInodeGetfile (fopId : FopsId) (priv : PrivateData) (flags : UInt32) : FS.M (Except Int FileId) :=
  anonInodeGetfileImpl fopId priv flags false

end Leanux
