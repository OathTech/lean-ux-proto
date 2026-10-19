import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterBoundaryFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTrafficNativeFrames

/-! Every original dispatcher arm preserves the native paired boundary.
Traffic selects its own actual residual carriers; retained calls use their
actual observer endpoints before existentially hiding the history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits

theorem dispatch (call : Syscall) : Preserves Boundary (Leanux.dispatch call) := by
  cases call
  case wgInject family port msg tos ll dest =>
    exact NativeFrames.socket _ _ Traffic.inject_boundary
  case wgFlood count port family messages => exact Traffic.flood_boundary
  case wgBatch items waitMs => exact Traffic.batch_boundary
  case wgObserve => exact NativeFrames.observe_dispatch
  case wgSet attrs => exact Dispatch.boundary _ (fun _ => Dispatch.configuration attrs)
  case wgGet ref => exact Dispatch.boundary _ (fun _ => Dispatch.get ref)
  case wgGetStart ref => exact Dispatch.boundary _ (fun _ => Dispatch.getStart ref)
  case wgGetRecv => exact Dispatch.boundary _ (fun _ => Dispatch.getRecv)
  case wgUp => exact Dispatch.boundary _ (fun _ => Dispatch.up)
  case wgXmit family addr payload opts =>
    exact Dispatch.boundary _ (fun _ => Dispatch.xmit family addr payload opts)
  case wgSetMtu n => exact Dispatch.boundary _ (fun _ => Dispatch.mtu n)
  case wgDeladdr family => exact Dispatch.boundary _ (fun _ => Dispatch.deladdr family)
  case wgDelroute family named dst plen oif typeCode metric =>
    exact Dispatch.boundary _ (fun _ => Dispatch.delroute family named dst plen oif typeCode metric)
  case wgAddroute dst plen oif typeCode metric mtu flags =>
    exact Dispatch.boundary _ (fun _ => Dispatch.addroute dst plen oif typeCode metric mtu flags)
  case wgAddaddr addr plen => exact Dispatch.boundary _ (fun _ => Dispatch.addaddr addr plen)
  case wgAdvance ticks => exact Dispatch.boundary _ (fun _ => Dispatch.advance ticks)
  case wgCreate => exact Dispatch.boundary _ (fun _ => Dispatch.create)
  case wgDown => exact Dispatch.boundary _ (fun _ => Lifecycle.down_dispatch)
  case wgDelete => exact Dispatch.boundary _ (fun _ => Lifecycle.delete_dispatch)
  case wgNetnsClose => exact Dispatch.boundary _ (fun _ => Dispatch.namespaceClose)
  all_goals exact Dispatch.boundary _ (fun _ => Dispatch.ordinary _ (by trivial))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Outer
