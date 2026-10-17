import Leanux.Proofs.WG.Queues.TxLiveTraffic
import Leanux.Proofs.WG.Queues.HolderEntryPollFree
import Leanux.Proofs.WG.Lifetimes.SyscallPreservation

/-! Concrete descriptor, route and transmit dispatch leaves. Callback wrappers
remain arbitrary product actions with explicit contracts at their source cuts. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveDispatch
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open LiveFrontier RxCredits

theorem stored (frame : SameProductStore action) : Preserves (fun w : World=>Ready w.wg) action :=
  frame.wp (fun s : ProductStore43=>Ready {dev:=s.2.2.2.dev})

theorem ambient (a : AmbientM α) : Preserves (fun w : World=>Ready w.wg) (liftAmbient a) :=
  productAmbient_spec a _ (fun _ _ hi=>hi)

theorem fs (a : FS.M α) : Preserves (fun w : World=>Ready w.wg) (liftFS a) :=
  productFS_spec a _ (fun _ _ _ _ hi=>hi)

theorem task (a : TaskM α) : Preserves (fun w : World=>Ready w.wg) (liftTask a) :=
  productTask_spec a _ (fun _ _ _ hi=>hi)

theorem seccomp (a : Seccomp.M α) : Preserves (fun w : World=>Ready w.wg) (liftSeccomp a) :=
  productSeccomp_spec a _ (fun _ _ _ _ hi=>hi)

theorem routing (a : Net.M α) : Preserves (fun w : World=>Ready w.wg) (monadLift a : Leanux.M α) :=
  stored (fun initial=>productRouting_spec a (fun s=>s=initial))

theorem socket (fd : Nat) (body : Leanux.M Int)
    (keeps : Preserves (fun w : World=>Ready w.wg) body) :
    Preserves (fun w : World=>Ready w.wg) (Leanux.socketCallOn fd body) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryPollFree.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryPollFree.socket_spec)
    _ (fun _ _ same hi=>LiveTraffic.wg_store same hi) fd body keeps

theorem rtnetlink (body : Leanux.M Int)
    (keeps : Preserves (fun w : World=>Ready w.wg) body) :
    Preserves (fun w : World=>Ready w.wg) (Leanux.rtnetlinkRequest body) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryPollFree.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryPollFree.rtnetlink_spec)
    _ (fun _ _ same hi=>LiveTraffic.wg_store same hi) body keeps

macro "live_dispatch_step" : tactic => `(tactic| first
  | (allocation_release_lift_from FS.M; exact fs _)
  | (allocation_release_lift_from TaskM; exact task _)
  | (allocation_release_lift_from AmbientM; exact ambient _)
  | (allocation_release_lift_from Seccomp.M; exact seccomp _)
  | (allocation_release_lift_from Net.M; exact routing _)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ hi=>hi) (fun _ _ hi=>hi.2))
  | (rx_retention_head modify; apply hoare_modify; intro w hi; exact LiveTraffic.wg_store rfl hi)
  | (rx_retention_head getWG; exact stored (fun initial=>productGetWG_spec (fun s=>s=initial)))
  | (rx_retention_head getRouting;
     exact stored (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v run; cases run; rfl))
  | (rx_retention_head modifyRouting; exact routing _)
  | rx_retention_step)

theorem netlink (body : Leanux.M Int)
    (keeps : Preserves (fun w : World=>Ready w.wg) body) :
    Preserves (fun w : World=>Ready w.wg) (Leanux.netlinkRequest body) := by
  unfold netlinkRequest socketCall
  simp (config := {zeta := false}) only [skipCut]
  repeat' first
    | (rx_retention_head socketCallOn; apply socket)
    | live_dispatch_step
    | (run_tac
         let target ← Lean.Elab.Tactic.getMainTarget
         let some action := target.getAppArgs.back? | throwError "missing source action"
         unless action.consumeMData.headBeta.isFVar do throwError "not the callback"
       exact keeps)

theorem delroute (family : Nat) (named : Bool) (dst plen oif typeCode metric : Nat) :
    Preserves (fun w : World=>Ready w.wg) (Env.wgDelroute family named dst plen oif typeCode metric) := by
  unfold Env.wgDelroute
  simp (config := {zeta := false}) only [unsupported]
  repeat' live_dispatch_step

theorem addroute (dst plen oif typeCode metric mtu flags : Nat) :
    Preserves (fun w : World=>Ready w.wg) (Env.wgAddroute dst plen oif typeCode metric mtu flags) := by
  unfold Env.wgAddroute
  simp (config := {zeta := false}) only [invariant]
  repeat' live_dispatch_step

theorem addaddr (addr plen : Nat) :
    Preserves (fun w : World=>Ready w.wg) (Env.wgAddaddr addr plen) := by
  unfold Env.wgAddaddr
  simp (config := {zeta := false}) only [unsupported]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World=>Ready w.wg)
       intro _ _
       change Preserves (fun w : World=>Ready w.wg) _)
    | live_dispatch_step

theorem xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Preserves (fun w : World=>Ready w.wg) (Leanux.dispatch (.wgXmit family addr payload opts)) := by
  unfold Leanux.dispatch socketCallOn
  simp (config := {zeta := false}) only [unsupported,Env.fixtureSend,skipCut]
  repeat' first
    | (allocation_release_lift_from WG.M
       exact PublicationPoll.native_product Ready _ (LiveFrontier.transmit _ _ _ _))
    | (rx_retention_head Env.xmitMulticastLoop; exact stored
        ((pinned_const _private.Leanux.Proofs.WG.Queues.BatchAccount.«0».Leanux.Proofs.WG.Queues.RxCredits.BatchAccount.multicast_store) _ _))
    | (rx_retention_head Env.xmitPackets; exact stored (xmitPackets_sameKernel _ _ _ _))
    | live_dispatch_step

theorem observe : PrefixPreserves LiveScheduler.Inv (fun _=>True) RxHistory.observe :=
  PrefixPreserves.bind LiveDeferred.idle (fun _=>
    LiveTraffic.observed _ _ (Appends.lift _) (erasesPrefix_lift _) (stored observeTail_sameKernel))

theorem observe_native : Preserves (fun w : World=>Ready w.wg) Env.observe :=
  LiveTraffic.native _ _ RxHistory.observe_erases observe

end Leanux.Proofs.WG.Queues.TxDisposition.LiveDispatch
