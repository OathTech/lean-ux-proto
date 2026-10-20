import Leanux.Proofs.WG.Progress.TrafficFiniteSource
import Leanux.Proofs.WG.Progress.ObservationFiniteSource
import Leanux.Proofs.WG.Progress.ConfigurationFiniteSource
import Leanux.Proofs.WG.Progress.LifecycleFiniteSource
import Leanux.Proofs.WG.Progress.LifecycleEnvironmentFiniteSource
import Leanux.Proofs.WG.Progress.FsNamespaceFiniteSource
import Leanux.Proofs.WG.Progress.FsEventfdFiniteSource
import Leanux.Proofs.WG.Progress.FsReadWriteFiniteSource
import Leanux.Proofs.WG.Progress.FsPipeDescriptorFiniteSource
import Leanux.Proofs.WG.Progress.FsFcntlFiniteSource
import Leanux.Proofs.WG.Progress.FsEpollControlFiniteSource
import Leanux.Proofs.WG.Progress.FsEpollWaitFiniteSource
import Leanux.Proofs.WG.Progress.SeccompInstallFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.DispatchFinite
open Leanux Leanux.WG

/-- Complete constructor selection with concrete finite replacements.
Retained arms are listed explicitly: native bounded dumps, routing,
packet admission/transmit, time advance, and runtime Seccomp execution.
They neither install a filter nor execute queued handshake work. -/
def call : Syscall → Leanux.M Int
  | .eventfd2 count flags => liftFS (FsFinite.sysEventfd2 count flags)
  | .dup fd => liftFS (FsFinite.sysDup fd)
  | .dup3 oldfd newfd flags => liftFS (FsFinite.ksysDup3 oldfd newfd flags)
  | .close fd => liftFS (FsFinite.sysClose fd)
  | .read fd count => liftFS (FsFinite.ksysRead fd count)
  | .write fd count buf => liftFS (FsFinite.ksysWrite fd buf count)
  | .pipe2 flags => liftFS (FsFinite.sysPipe2 flags)
  | .fcntl fd cmd arg => liftFS (FsFinite.sysFcntl fd cmd arg)
  | .epollCreate1 flags => liftFS (FsFinite.sysEpollCreate1 flags)
  | .epollCtl epfd op fd events data => liftFS (FsFinite.sysEpollCtl epfd op fd events data)
  | .epollWait epfd maxevents timeout => liftFS (FsFinite.sysEpollWait epfd maxevents timeout)
  | .wgSet attrs => netlinkRequest (liftWG (ConfigurationFinite.device attrs))
  | .wgUp => socketCallOn SENDER_FD LifecycleFinite.envUp
  | .wgDown => socketCallOn SENDER_FD LifecycleFinite.envDown
  | .wgDelete => rtnetlinkRequest LifecycleFinite.envDelete
  | .wgNetnsClose => FsFinite.netnsClose
  | .wgInject family port message tos ll dest =>
      socketCallOn SENDER_FD (TrafficFinite.nativeInject family port message tos ll dest)
  | .wgFlood count port family messages => TrafficFinite.nativeFlood count port family messages
  | .wgBatch items _ => TrafficFinite.nativeBatch items
  | .wgObserve => do
    let (ret, observed) ← ObservationFinite.observe
    modifyAmbient fun w => { w with extraOut :=
      ["datagrams", "replies", "stats"].map fun k => (k, observed.getObjValD k) }
    socketCallOn LISTEN4_FD (pure ret)
  | .seccompInstall via flags filter len bad mode =>
      liftSeccomp (SeccompInstallFinite.install via flags filter len bad mode)
  | c@(.wgGet _) => Leanux.dispatch c
  | c@(.wgGetStart _) => Leanux.dispatch c
  | c@(.wgGetRecv) => Leanux.dispatch c
  | c@(.wgXmit ..) => Leanux.dispatch c
  | c@(.wgSetMtu _) => Leanux.dispatch c
  | c@(.wgDeladdr _) => Leanux.dispatch c
  | c@(.wgDelroute ..) => Leanux.dispatch c
  | c@(.wgAddroute ..) => Leanux.dispatch c
  | c@(.wgAddaddr ..) => Leanux.dispatch c
  | c@(.wgAdvance _) => Leanux.dispatch c
  | c@(.wgCreate) => Leanux.dispatch c
  | c@(.seccompProbe ..) => Leanux.dispatch c
  | c@(.seccompPrctl ..) => Leanux.dispatch c
  | c@(.seccompCapdrop) => Leanux.dispatch c
  | c@(.seccompQuery ..) => Leanux.dispatch c

theorem call_source (c : Syscall) : Leanux.dispatch c = call c := by
  cases c <;> simp only [call, Leanux.dispatch,
    ← FsFinite.sysEventfd2_source, ← FsFinite.sysDup_source, ← FsFinite.ksysDup3_source,
    ← FsFinite.sysClose_source, ← FsFinite.ksysRead_source, ← FsFinite.ksysWrite_source,
    ← FsFinite.sysPipe2_source, ← FsFinite.sysFcntl_source, ← FsFinite.sysEpollCreate1_source,
    ← FsFinite.sysEpollCtl_source, ← FsFinite.sysEpollWait_source,
    ← ConfigurationFinite.device_source, ← LifecycleFinite.envUp_source,
    ← LifecycleFinite.envDown_source, ← LifecycleFinite.envDelete_source,
    ← FsFinite.netnsClose_source, ← TrafficFinite.nativeInject_source,
    ← TrafficFinite.nativeFlood_source, ← TrafficFinite.nativeBatch_source,
    ← ObservationFinite.observe_source, ← SeccompInstallFinite.install_source]
  all_goals rfl

end Leanux.Proofs.WG.Progress.DispatchFinite
