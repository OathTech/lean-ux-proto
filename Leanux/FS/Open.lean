import Leanux.FS.FileTable

/-!
# fs/open.c — `filp_flush` and `filp_close`

The `close` syscall itself is in `Leanux.FS.Close` because it needs
`file_close_fd` from fs/file.c, which in turn needs `filp_close`.
-/

namespace Leanux

/-- filp_flush (open.c:1522-1540). `dnotify_flush` is compiled out
    (`CONFIG_DNOTIFY=n`); `locks_remove_posix` is a cut point (no POSIX locks). -/
def filpFlush (fid : FileId) : M Int := do
  let f ← getFile fid
  -- CHECK_DATA_CORRUPTION(file_count(filp) == 0, ...)
  if ← branch .filpFlushCountZero (f.fCount == 0) then return 0
  let fop ← fopsOf f.fOp
  if ← branch .filpFlushHasFlush fop.flush then
    unsupported "f_op->flush"
  if ← branch .filpFlushNotPath (!hasFlag f.fMode FMODE_PATH) then
    pure ()  -- dnotify_flush; locks_remove_posix
  return 0

/-- filp_close (open.c:1542-1550). -/
def filpClose (fid : FileId) : M Int := do
  let retval ← filpFlush fid
  fput fid
  return retval

end Leanux
