import Leanux.FS.File
import Leanux.FS.Fput

/-!
# fs/open.c — the `close` syscall
-/

namespace Leanux

/-- SYSCALL_DEFINE1(close) (open.c:1558-1583). -/
def sysClose (fd : Nat) : FS.M Int := do
  let file ← fileCloseFd fd
  if ← branch .closeNoFile file.isNone then return -EBADF
  let some fid := file | invariant "unreachable"
  let retval ← filpFlush fid
  -- "We're returning to user space. Don't bother with any delayed fput() cases."
  fputSync fid
  -- `unlikely(retval == -ERESTARTSYS || retval == -ERESTARTNOINTR ||
  --          retval == -ERESTARTNOHAND || retval == -ERESTART_RESTARTBLOCK)`
  let restart ← do
    if ← branch .closeRestartSys (retval == -512) then pure true
    else if ← branch .closeRestartNoIntr (retval == -513) then pure true
    else if ← branch .closeRestartNoHand (retval == -514) then pure true
    else branch .closeRestartBlock (retval == -516)
  if restart then return -4  -- -EINTR
  return retval

end Leanux
