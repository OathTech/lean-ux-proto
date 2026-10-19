import Leanux.Proofs.WG.Progress.FsDescriptorCallerFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-- The namespace-holder close sequence uses the original fixed descriptor
list and performs return-to-user work after each successful close. -/
def netnsCloseWith (close : Nat → FS.M Int) (work : FS.M Unit) : Leanux.M Int := do
  if !(← getRouting).foreignCreator then unsupported "wg_netns_close outside the foreign-creator fixture"
  if (← getEnv).netnsCHolders.isEmpty then unsupported "wg_netns_close twice"
  for fd in [INJECT_FD, LISTEN6_FD, LISTEN4_FD, PIN_FD] do
    let ret ← close fd
    if ret != 0 then invariant s!"close({fd}) of a fixture holder returned {ret}"
    work
  return 0

theorem netnsClose_factor :
    Leanux.netnsClose = netnsCloseWith Leanux.sysClose Leanux.taskWorkRun := rfl

/-- Concrete finite close and release callbacks; the namespace cleanup queue
record and all native refusals remain in their original positions. -/
def netnsClose : Leanux.M Int := netnsCloseWith sysClose taskWorkRun

theorem netnsClose_source : Leanux.netnsClose = netnsClose := by
  rw [netnsClose_factor, funext sysClose_source, taskWorkRun_source]
  rfl

end Leanux.Proofs.WG.Progress.FsFinite
