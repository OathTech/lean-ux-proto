import Leanux.Proofs.WG.TimerDiscipline.HookMaintenanceHistoryFrames
import Leanux.Proofs.WG.TimerDiscipline.HookSyscallSource
import Leanux.Proofs.WG.TimerDiscipline.SessionFrontierBridge
import Leanux.Proofs.WG.Keypairs.Evolution.Syscalls
import Leanux.Proofs.WG.Queues.RoutingDispatchFrame

/-! Counter-frontier transport through configuration and lifecycle uses the
landed ordinary-action relation, without another traversal of those callers. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Leanux Leanux.WG Leanux.Proofs.Logged HandshakeJournal Lifetimes Configuration

theorem peerCommand_frontier (attrs : PeerAttrs) :
    StatePrefixPreserves (fun h g _=>Frontier h g.keypairCounter) Ordered (peerCommand attrs) :=
  native_observer_frontier _ _ (peerCommand_appends attrs) (peerCommand_erases attrs)
    (peerCommand_ids attrs) (ordinary_counter (Keypairs.WGConfig.setPeerCmd_ordinary attrs))

theorem deviceCommand_frontier (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h g _=>Frontier h g.keypairCounter) Ordered (deviceCommand attrs) :=
  native_observer_frontier _ _ (deviceCommand_appends attrs) (deviceCommand_erases attrs)
    (deviceCommand_ids attrs) (ordinary_counter (Keypairs.WGConfig.wgSetDevice_ordinary attrs))

theorem set_frontier (attrs : DeviceAttrs) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered (set attrs) :=
  observer_frontier _ _ (netlinkRequestWith_appends (deviceCommand_appends attrs).liftWGObserver)
    (set_erases attrs)
    (netlinkRequestWith_frame Event.sessionId (deviceCommand_ids attrs).liftWGObserver)
    (product_ordinary_counter (Keypairs.SyscallObservers.dispatch_noReceive_ordinary (.wgSet attrs) True.intro))

theorem down_frontier :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered down :=
  observer_frontier _ _ (socketCallOnWith_appends _ HandshakeMaintenance.envDown_appends) down_erases
    (socketCallOnWith_frame Event.sessionId _ HandshakeMaintenance.envDown_ids)
    (product_ordinary_counter (Keypairs.SyscallObservers.dispatch_noReceive_ordinary .wgDown True.intro))

theorem delete_frontier :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered delete :=
  observer_frontier _ _ (rtnetlinkRequestWith_appends HandshakeMaintenance.envDelete_appends) delete_erases
    (rtnetlinkRequestWith_frame Event.sessionId HandshakeMaintenance.envDelete_ids)
    (product_ordinary_counter (Keypairs.SyscallObservers.dispatch_noReceive_ordinary .wgDelete True.intro))

theorem retained_frontier (c : Syscall) (selected : DispatchRetained c) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered (retained c) := by
  have noReceive : Keypairs.SyscallObservers.NoReceiveDispatch c := by
    cases c <;> simp_all [DispatchRetained,Keypairs.SyscallObservers.NoReceiveDispatch]
  cases c
  case wgDown => exact down_frontier
  all_goals exact quiet_frontier _ (product_ordinary_counter
    (Keypairs.SyscallObservers.dispatch_noReceive_ordinary _ noReceive))

theorem create_frontier :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered
      (liftPrefix (Leanux.dispatch .wgCreate)) :=
  quiet_frontier _ (product_ordinary_counter (Keypairs.SyscallObservers.dispatch_noReceive_ordinary .wgCreate True.intro))

theorem xmit_frontier (family addr : Nat) (bytes : List UInt8) (opts : Env.XmitOpts) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered
      (liftPrefix (Leanux.dispatch (.wgXmit family addr bytes opts))) :=
  quiet_frontier _ (product_ordinary_counter
    (Keypairs.SyscallObservers.dispatch_noReceive_ordinary (.wgXmit family addr bytes opts) True.intro))

end Leanux.Proofs.WG.TimerDiscipline.HookCommon
