import Leanux.Proofs.WG.Roaming.RemoteDispatchFrames
import Leanux.Proofs.WG.Config.DispatchRulesSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDispatch
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open RemoteSilent

theorem dispatch_contracts (entry : RemoteMap) : Config.DispatchRules.Contracts (Retained entry) where
  stable w v same pre := by
    have destinations := congrArg (fun s : WGStoreView=>fun pid : PeerId=>
      ((s.dev.bind fun d=>d.peers[pid]?).bind Peer.endpoint).map destination) same
    change destinationAt v=destinationAt w at destinations
    change RemoteRetained entry (destinationAt v)
    rw [destinations]
    exact pre
  dump := RemoteLifecycle.dump entry
  dumpFrame action same := (RemoteDispatch.dump_frame action same).wp (RemoteRetained entry)
  up := RemoteLifecycle.envUp_native entry
  down := RemoteLifecycle.envDown_native entry
  mtu n := (RemoteDispatch.mtu_frame n).wp (RemoteRetained entry)

theorem dump_dispatch (entry : RemoteMap) (device : DeviceRef) :
    Preserves (fun w : World=>Retained entry w.wg) (Leanux.dispatch (.wgGet device)) :=
  Config.DispatchRules.dump_dispatch (Retained entry) (dispatch_contracts entry) device

theorem dump_start (entry : RemoteMap) (device : DeviceRef) :
    Preserves (fun w : World=>Retained entry w.wg) (Leanux.dispatch (.wgGetStart device)) :=
  Config.DispatchRules.dump_start (Retained entry) (dispatch_contracts entry) device

theorem dump_receive (entry : RemoteMap) :
    Preserves (fun w : World=>Retained entry w.wg) (Leanux.dispatch .wgGetRecv) :=
  Config.DispatchRules.dump_receive (Retained entry) (dispatch_contracts entry)

theorem rtnetlink_retained (entry : RemoteMap) (body : Leanux.M Int)
    (kept : Preserves (fun w : World=>Retained entry w.wg) body) :
    Preserves (fun w : World=>Retained entry w.wg) (rtnetlinkRequest body) :=
  Config.DispatchRules.rtnetlink_retained (Retained entry) (dispatch_contracts entry) body kept

theorem advance (entry : RemoteMap) (ticks : Nat) :
    Preserves (fun w : World=>Retained entry w.wg) (Leanux.dispatch (.wgAdvance ticks)) :=
  Config.DispatchRules.advance (Retained entry) (dispatch_contracts entry) ticks

theorem ordinary (entry : RemoteMap) (call : Syscall)
    (selected : HolderEntryPollFree.Ordinary call) :
    Preserves (fun w : World=>Retained entry w.wg) (Leanux.dispatch call) :=
  Config.DispatchRules.ordinary (Retained entry) call selected

theorem retained (entry : RemoteMap) (call : Syscall) (selected : DispatchRetained call) :
    Preserves (fun w : World=>Retained entry w.wg) (Leanux.dispatch call) :=
  Config.DispatchRules.retained (Retained entry) (dispatch_contracts entry) call selected

theorem retained_covered (entry : RemoteMap) (call : Syscall) (selected : DispatchRetained call) :
    PrefixPreserves (RemoteDriver.Inv entry) RemoteDriver.Safe
      (RemoteDriver.focus (RxHistory.syscallDispatch call)) :=
  RemoteDriver.focus_retained entry _ _ (RxHistory.syscallDispatch_appends call)
    (RxHistory.syscallDispatch_erases call) (fun before=>retained before call selected)

end Leanux.Proofs.WG.Roaming.RemoteDispatch
