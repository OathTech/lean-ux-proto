import Leanux.FS.File

/-!
# fs/fcntl.c — `fcntl` for F_GETFD, F_SETFD and F_GETFL
-/

namespace Leanux

inductive FcntlCmd where
  | getFD | setFD | getFL
  deriving Repr, BEq

/-- do_fcntl (fcntl.c:443-...): the `switch (cmd)` arm taken is the choice
    point; only the three modeled commands can reach it. -/
def doFcntl (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) (fid : FileId) : M Int := do
  let argi : Int := (arg.toUInt32).toNat  -- (int)arg; only bit 0 is tested
  match cmd with
  | .getFD =>
    _ ← branch .fcntlCaseGetfd true
    let set ← getCloseOnExec fd
    _ ← branch .fcntlGetfdSet set  -- err = get_close_on_exec(fd) ? FD_CLOEXEC : 0
    return if set then FD_CLOEXEC else 0
  | .setFD =>
    _ ← branch .fcntlCaseSetfd true
    setCloseOnExec fd (argi % 2 == 1)  -- argi & FD_CLOEXEC
    return 0
  | .getFL =>
    _ ← branch .fcntlCaseGetfl true
    return (← getFile fid).fFlags.toNat

/-- SYSCALL_DEFINE3(fcntl) (fcntl.c:573-594). `security_file_fcntl` is the
    constant 0 (`CONFIG_SECURITY=n`), so `if (!err)` is not a branch here. -/
def sysFcntl (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) : M Int := do
  let f ← fdgetRaw fd
  let mut err := -EBADF
  if ← branch .fcntlNoFile f.file.isNone then return err  -- goto out
  let some fid := f.file | invariant "unreachable"
  if ← branch .fcntlPathFile (hasFlag (← getFile fid).fMode FMODE_PATH) then
    unsupported "check_fcntl_cmd for O_PATH files"
  err ← doFcntl fd cmd arg fid
  fdput f  -- out1:
  return err

end Leanux
