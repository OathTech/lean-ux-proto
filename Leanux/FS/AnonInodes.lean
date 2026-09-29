import Leanux.FS.FileTable

/-!
# fs/anon_inodes.c — `anon_inode_getfile`

The shared anonymous inode (`anon_inode_inode`), `ihold`/`iput`,
`module_put` and `f_mapping` are cut points. `private_data = priv` is
represented by the file's kind, which carries the eventfd context identity.
-/

namespace Leanux

/-- __anon_inode_getfile (anon_inodes.c:90-138). With `CONFIG_MODULES=n`,
    `try_module_get` is the constant `true`, so the owner test folds away. -/
def anonInodeGetfileImpl (fop : Fops) (kind : FileKind) (flags : UInt32) (makeInode : Bool) :
    M (Except Int FileId) := do
  if ← branch .anonGetfileOwner fop.owner then
    unsupported "try_module_get(fops->owner)"
  if ← branch .anonMakeInode makeInode then
    unsupported "anon_inode_make_secure_inode"
  -- inode = anon_inode_inode, set at boot by anon_inode_init
  if ← branch .anonInodeErr (← getK).anonInodeInodeErr then return .error (-19)  -- -ENODEV
  -- ihold(inode)
  let file ← allocFilePseudo (flags &&& (O_ACCMODE ||| O_NONBLOCK)) kind fop
  if ← branch .anonGetfileFileErr (file matches .error _) then
    return file  -- err_iput: iput(inode); err: module_put(fops->owner)
  -- file->f_mapping = inode->i_mapping; file->private_data = priv
  return file

/-- anon_inode_getfile (anon_inodes.c:156-161). -/
def anonInodeGetfile (fop : Fops) (kind : FileKind) (flags : UInt32) : M (Except Int FileId) :=
  anonInodeGetfileImpl fop kind flags false

end Leanux
