import Leanux.Proofs.WG.Origins.RetainingConfiguration
import Leanux.Proofs.WG.Lifetimes.DumpAccess
import Leanux.Proofs.WG.AllowedIps.RoutingDumpFrames

/-! Original dump callbacks and transport retain the complete receiving-material
view. Cursor references may be acquired or released; no cursor validity,
peer residency or successful completion is assumed. Stops have no endpoint. -/
namespace Leanux.Proofs.WG.Origins.Retaining
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Lifetimes Leanux.Proofs.WG.NetlinkDump Std.Do
set_option pp.structureInstances false

theorem dump_material (ha : SameDumpKernel a) : SameView view a := by
  apply ha.of_factor (fun k : Kernel=>k.wg.map materialState) view
  intro w
  rfl

theorem wgGetDeviceDone_material (ctx : DumpCtx) : SameView view (wgGetDeviceDone ctx) := by
  apply SameView.of_wp
  intro s
  have hp := (peerPut_material ctx.nextPeer).wp (fun t=>t=s)
  mvcgen [wgGetDeviceDone,hp,branch]

theorem deviceDumpHeader_material (d : Device) (ctx : DumpCtx) (seq : Nat) (skb : NlSkb) :
    SameView view (deviceDumpHeaderSource d ctx seq skb) :=
  kernel (deviceDumpHeader_sameKernel d ctx seq skb)

theorem deviceDumpTail_material (d : Device) (ctx : DumpCtx) (skb : NlSkb)
    (flags : Nat) (attrs : List (String×Lean.Json)) :
    SameView view (deviceDumpTailSource d ctx skb flags attrs) := by
  apply SameView.of_wp
  intro s
  have hg := material_getPeer (fun t=>t=s)
  have hd := fun pid c b => (kernel (getPeerDump_sameKernel pid c b)).wp (fun t=>t=s)
  have hr := fun pid => (peerGet_material pid).wp (fun t=>t=s)
  have hp := fun peer => (peerPut_material peer).wp (fun t=>t=s)
  have hl (α β : Type) := list_view_spec view (α:=α) (β:=β) (fun t=>t=s)
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,deviceDumpTailSource,
    hg,hd,hr,hp,WG.andM,WG.orM,requireNotPending,branch,invariant,unsupported]
  all_goals try exact ((⇓? _ w=>⌜view w=s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem wgGetDeviceDump_material (ctx : DumpCtx) (seq : Nat) (skb : NlSkb) :
    SameView view (wgGetDeviceDump ctx seq skb) := by
  rw [wgGetDeviceDump_source]
  apply SameView.of_wp
  intro s
  have hh := fun d => (deviceDumpHeader_material d ctx seq skb).wp (fun t=>t=s)
  have ht := fun d b f a => (deviceDumpTail_material d ctx b f a).wp (fun t=>t=s)
  mvcgen [hh,ht,getDev,getK,invariant]

theorem netlinkDump_material (fd : Nat) : SameView view (netlinkDump fd) := by
  apply SameView.of_wp
  intro s
  have hg := (kernel (getNlSock_sameKernel fd)).wp (fun t=>t=s)
  have hs := fun sock => (dump_material (setNlSock_sameDumpKernel fd sock)).wp (fun t=>t=s)
  have hd := fun ctx seq skb => (wgGetDeviceDump_material ctx seq skb).wp (fun t=>t=s)
  have he := fun ctx => (wgGetDeviceDone_material ctx).wp (fun t=>t=s)
  mvcgen [netlinkDump,hg,hs,hd,he]

theorem netlinkDumpStart_material (fd : Nat) (ref : DeviceRef) : SameView view (netlinkDumpStart fd ref) := by
  apply SameView.of_wp
  intro s
  have hg := (kernel (getNlSock_sameKernel fd)).wp (fun t=>t=s)
  have hs := fun sock => (dump_material (setNlSock_sameDumpKernel fd sock)).wp (fun t=>t=s)
  have hl := (kernel (lookupInterface_sameKernel ref)).wp (fun t=>t=s)
  have hd := (netlinkDump_material fd).wp (fun t=>t=s)
  mvcgen [netlinkDumpStart,hg,hs,hl,hd,branch,invariant,unsupported]

theorem netlinkRecvmsg_material (fd : Nat) : SameView view (netlinkRecvmsg fd) := by
  apply SameView.of_wp
  intro s
  have hg := (kernel (getNlSock_sameKernel fd)).wp (fun t=>t=s)
  have hs := fun sock => (dump_material (setNlSock_sameDumpKernel fd sock)).wp (fun t=>t=s)
  have hd := (netlinkDump_material fd).wp (fun t=>t=s)
  mvcgen [netlinkRecvmsg,hg,hs,hd]

theorem wgGetDevice_material (ref : DeviceRef) : SameView view (wgGetDevice ref) := by
  apply SameView.of_wp
  intro s
  have hs := (netlinkDumpStart_material 7 ref).wp (fun t=>t=s)
  have hr := (netlinkRecvmsg_material 7).wp (fun t=>t=s)
  have hc := fun ms => (kernel (coalesce_sameKernel ms)).wp (fun t=>t=s)
  have hl (α β : Type) := list_view_spec view (α:=α) (β:=β) (fun t=>t=s)
  mvcgen [-Std.Do.Spec.forIn_list,-Std.Do.Spec.forIn'_list,hl,wgGetDevice,hs,hr,hc,invariant]
  all_goals try exact ((⇓? _ w=>⌜view w=s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals trivial

end Leanux.Proofs.WG.Origins.Retaining
