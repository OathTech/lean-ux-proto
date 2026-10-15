import Leanux.Proofs.WG.AllowedIps.RoutingEnvTrafficFrames
import Leanux.Proofs.WG.Configuration.LifecycleCompletion

/-! Environment controls retain routing at normal endpoints. Device deletion
uses the actual lifecycle completion observer, so its completed clear/removal
cuts survive later Stops without asserting a failed World. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem envScalar_routing (a : M α) (ha : SameEnvScalar a) : SameView routingView a :=
  ha.of_factor (fun k => k.wg.map routingState) routingView (fun _ => by simp only [routingView, envScalarView, envScalarKernel, envScalarDevice, Option.map_map, Function.comp_def]; rfl)

theorem requireIdleDevice_routing : SameView routingView Env.requireIdleDevice := by
  apply SameView.of_wp
  intro s
  have hn := requireNoCryptWork_routing.wp (fun t => t = s)
  mvcgen [Env.requireIdleDevice, hn, getDev, getK, invariant, unsupported]

theorem envWgUp_routing : RetainsRoutingCall Env.wgUp := by
  apply ProjectedAction.of_wp
  intro s
  have hu := wgUp_routing.wp s
  have hc := (routing_kernel _ (skipCut_sameKernel allocCuts)).wp (RetainsRouting s)
  mvcgen [Env.wgUp, hu, hc, getK]
  all_goals try simp_all [routingView]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem envWgDown_routing : RetainsRoutingCall Env.wgDown := by
  apply ProjectedAction.of_wp
  intro s
  have hi := requireIdleDevice_routing.wp (RetainsRouting s)
  have hd := wgDown_routing.wp s
  have hc := (routing_kernel _ (skipCut_sameKernel allocCuts)).wp (RetainsRouting s)
  mvcgen [Env.wgDown, hi, hd, hc, getK]
  all_goals try simp_all [routingView]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem envSetMtu_routing (mtu : Nat) : SameView routingView (Env.setMtu mtu) :=
  envScalar_routing _ (setMtu_sameEnvScalar mtu)

theorem routeIntoWg0_routing : SameView routingView Env.routeIntoWg0 :=
  routing_kernel _ routeIntoWg0_sameKernel

theorem wgDeladdr_routing (family : Nat) : SameView routingView (Env.wgDeladdr family) :=
  routing_kernel _ (wgDeladdr_sameKernel family)

theorem wgDelroute_routing (family : Nat) : SameView routingView (Env.wgDelroute family) :=
  routing_kernel _ (wgDelroute_sameKernel family)

theorem observe_routing : RetainsRoutingCall Env.observe := by
  rw [Environment.observe_eq]
  apply ProjectedAction.of_wp
  intro s
  have hi := idleTimers_routing.wp s
  have ht := (routing_kernel _ observeTail_sameKernel).wp (RetainsRouting s)
  mvcgen [hi, ht]
  subst s
  exact RetainsRouting.refl _

theorem netnsCleanup_routing : RetainsRoutingCall Env.netnsCleanup := by
  have hb : RetainsRoutingCall (do WG.netnsPreExit; skipCut ([.dstCacheResetTs] ++ allocCuts)) := by
    apply ProjectedAction.of_wp
    intro s
    have hn := netnsPreExit_routing.wp (RetainsRouting s)
    have hc := (routing_kernel _ (skipCut_sameKernel ([.dstCacheResetTs] ++ allocCuts))).wp (RetainsRouting s)
    mvcgen [hn, hc]
    subst s
    exact RetainsRouting.refl _
  apply ProjectedAction.of_wp
  intro s
  have hp := (routing_kernel _ (peekUnit_sameKernel .netnsCleanup)).wp (RetainsRouting s)
  have hr := fun u => (routing_kernel _ (resolveUnit_sameKernel .netnsCleanup u [0])).wp (RetainsRouting s)
  have hw := (runWorker_routing .netnsCleanup _ hb).wp s
  mvcgen [Env.netnsCleanup, hp, hr, hw, unsupported]
  all_goals try simp_all [routingView]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

def envWgDeleteObserved : PrefixM RoutingCompletion Int := do
  if (← liftPrefix getK).wg.isSome then liftPrefix Env.requireIdleDevice
  let pending (sock : WG.NlSock) : Bool :=
    sock.cbRunning || sock.queue.any fun chunk => chunk.messages.any fun m => match m with | .done .. => true | _ => false
  let k ← liftPrefix getK
  if pending k.nlSock7 || pending k.nlSock8 then
    liftPrefix (unsupported "a delete with a stepped dump pending (the dump's cursor holds the device reference; the guest refuses wg_delete_with_dump_pending)")
  let ret ← Configuration.wgDeleteObserved
  liftPrefix (modify fun w => {w with addrs4 := [], addrs6 := [], defaultRoute4 := false, defaultRoute6 := false, ipv4Gen := w.ipv4Gen + 1, ipv6Gen := w.ipv6Gen + 1})
  return ret

theorem envWgDeleteObserved_erases : ErasesPrefix envWgDeleteObserved Env.wgDelete := by
  unfold envWgDeleteObserved Env.wgDelete
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact Configuration.wgDeleteObserved_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)
  all_goals contradiction

theorem envWgDeleteObserved_global (initial : FlatTable × FlatTable) :
    PrefixPreserves (GlobalCompletionState initial) (CompletionSafe initial) envWgDeleteObserved := by
  have safe : ∀ h w, GlobalCompletionState initial h w → CompletionSafe initial h := fun _ _ hi => hi.1
  unfold envWgDeleteObserved
  repeat' first
    | with_reducible exact Configuration.wgDeleteObserved_global initial
    | with_reducible exact global_completion_same initial _ requireIdleDevice_routing
    | (solve | apply global_completion_same initial; apply routing_kernel; intro w x v hr; cases hr; rfl)
    | (solve | apply global_completion_same initial; apply routing_kernel; intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

end Leanux.Proofs.WG.AllowedIps
