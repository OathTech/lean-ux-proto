import Leanux.Proofs.WG.AllowedIps.RoutingEnvControlsCompletion
import Leanux.Proofs.WG.Lifetimes.DumpAccess

/-! Stepped and whole netlink dumps retain routing at normal endpoints. Their
actual cursor acquisition/release can retire peers; no cursor-validity or
successful-drain premise is required. Socket/serialization frames retain the
complete routing projection, and all original Stops remain observable. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.WG.NetlinkDump Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem dumpKernel_routing (a : M α) (ha : SameDumpKernel a) : SameView routingView a :=
  ha.of_factor (fun k => k.wg.map routingState) routingView (fun _ => rfl)

theorem wgGetDeviceDone_routing (ctx : DumpCtx) : RetainsRoutingCall (wgGetDeviceDone ctx) := by
  apply ProjectedAction.of_wp
  intro s
  have hp := (peerPut_retainsRouting ctx.nextPeer).wp s
  mvcgen [wgGetDeviceDone, hp, branch]
  subst s
  exact RetainsRouting.refl _

theorem deviceDumpTail_routing (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String × Lean.Json)) :
    RetainsRoutingCall (deviceDumpTailSource d ctx skb flags attrs) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := fun pid => (getPeer_routing pid).wp P
  have hn := fun pid => (requireNotPending_routing pid "dumping the peer").wp P
  have hd := fun pid ctx skb => (routing_kernel _ (getPeerDump_sameKernel pid ctx skb)).wp P
  have hget := fun pid => (peerGet_routing pid).wp P
  have hput := fun pid => (peerPut_retainsRouting pid).wp s
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    deviceDumpTailSource, hg, hn, hd, hget, hput, WG.orM, WG.andM, branch, invariant, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try trivial
  all_goals try exact id
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem wgGetDeviceDump_routing (ctx : DumpCtx) (prevSeq : Nat) (skb : NlSkb) :
    RetainsRoutingCall (wgGetDeviceDump ctx prevSeq skb) := by
  rw [wgGetDeviceDump_source]
  apply ProjectedAction.of_wp
  intro s
  have hh := fun d => (routing_kernel _ (deviceDumpHeader_sameKernel d ctx prevSeq skb)).wp (RetainsRouting s)
  have ht := fun d skb flags attrs => (deviceDumpTail_routing d ctx skb flags attrs).wp s
  mvcgen [hh, ht, getDev, getK, invariant]
  all_goals try simp_all [routingView]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem netlinkDump_routing (fd : Nat) : RetainsRoutingCall (netlinkDump fd) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := (routing_kernel _ (getNlSock_sameKernel fd)).wp P
  have hs := fun sock => (dumpKernel_routing _ (setNlSock_sameDumpKernel fd sock)).wp P
  have hd := fun ctx seq skb => (wgGetDeviceDump_routing ctx seq skb).wp s
  have hf := fun ctx => (wgGetDeviceDone_routing ctx).wp s
  mvcgen [netlinkDump, hg, hs, hd, hf]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem netlinkDumpStart_routing (fd : Nat) (ref : DeviceRef) :
    RetainsRoutingCall (netlinkDumpStart fd ref) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := (routing_kernel _ (getNlSock_sameKernel fd)).wp P
  have hs := fun sock => (dumpKernel_routing _ (setNlSock_sameDumpKernel fd sock)).wp P
  have hl := (routing_kernel _ (lookupInterface_sameKernel ref)).wp P
  have hd := (netlinkDump_routing fd).wp s
  mvcgen [netlinkDumpStart, hg, hs, hl, hd, branch, invariant, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem netlinkRecvmsg_routing (fd : Nat) : RetainsRoutingCall (netlinkRecvmsg fd) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := (routing_kernel _ (getNlSock_sameKernel fd)).wp P
  have hs := fun sock => (dumpKernel_routing _ (setNlSock_sameDumpKernel fd sock)).wp P
  have hd := (netlinkDump_routing fd).wp s
  mvcgen [netlinkRecvmsg, hg, hs, hd]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem wgGetDevice_routing (ref : DeviceRef) : RetainsRoutingCall (wgGetDevice ref) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hs := (netlinkDumpStart_routing 7 ref).wp s
  have hr := (netlinkRecvmsg_routing 7).wp s
  have hc := fun ms => (routing_kernel _ (coalesce_sameKernel ms)).wp P
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    wgGetDevice, hs, hr, hc, invariant]
  all_goals try exact ((⇓? _ w => ⌜RetainsRouting s (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try trivial
  all_goals try exact id
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

end Leanux.Proofs.WG.AllowedIps
