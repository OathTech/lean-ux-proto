import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierWorkers

/-! The common draining scheduler uses its real copied consistency trials;
only committed worker iterations and NAPI dispatch affect this shared carrier. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues TransmitSecurity.Driver
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
variable {E : Type} {extra : List E → Prop}
  {origin : E → Option TransportDriver.OriginEvent} {replay : E → Option TransportDriver.Replay}
  {hooks : Hooks E}

theorem modifyDev_rx (f : Device → Device) (epoch : ∀ d, (f d).ifindex = d.ifindex)
    (packets : ∀ d, (f d).rxSkbs = d.rxSkbs) :
    SameView RxDisposition.nativeRxStore (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  cases run
  simp only [RxDisposition.nativeRxStore,Option.map_map,Option.bind_map,Function.comp_def,epoch,packets]

theorem getTxSkb_rx (skb : SkbId) : SameView RxDisposition.nativeRxStore (getTxSkb skb) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a pkt v b run
  exact congrArg _ (Packets.getTxSkb_current skb w v pkt a b run).1

theorem product_ite (p : Prop) [Decidable p] {a b : PrefixM E α}
    (ha : p → ProductSafe extra origin replay a) (hb : ¬p → ProductSafe extra origin replay b) :
    ProductSafe extra origin replay (if p then a else b) := PrefixPreserves.ite p ha hb

theorem product_throw (err : Stop) :
    ProductSafe extra origin replay (liftPrefix (throw err : Leanux.M α)) := by
  intro w h hi
  exact ⟨[], by simp, hi.2, True.intro⟩

open Lean Meta Elab Tactic in
elab "transport_product_native " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductSafe do throwError "not a product carrier contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``liftPrefix do throwError "not a native product lift"
  let native := action.getAppArgs.back!.consumeMData.headBeta
  let .const actual _ := native.getAppFn | throwError "not a native constant"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different native head"

macro "transport_scheduler_native" : tactic => `(tactic| first
  | (transport_product_native liftWG
     apply product_wg
     first
     | (snapshot_head getTxSkb; exact getTxSkb_rx _)
     | (snapshot_head modifyDev; apply modifyDev_rx <;> intro d <;> rfl)
     | solve | transport_native_rx)
  | (first | transport_product_native getAmbient | transport_product_native modifyAmbient
           | transport_product_native peekHiddenSite | transport_product_native invariant
     exact product_ambient _)
  | (transport_product_native throw
     apply PrefixEnsures.lift _ (fun _ _ hi => hi.2)
     intro h w x v hi run
     cases run))

macro "transport_carrier_product_step" : tactic => `(tactic| first
  | (transport_carrier_head Pure.pure; exact product_pure _)
  | (transport_carrier_head Bind.bind; apply product_bind)
  | (transport_carrier_head ite; apply product_ite)
  | transport_carrier_join_let
  | transport_carrier_join_use
  | maintenance_intro
  | transport_carrier_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem cryptAhead (h : WorkerSafe extra origin replay hooks) (pid : PeerId) :
    ProductSafe extra origin replay (cryptAheadObserved hooks pid) := by
  unfold cryptAheadObserved
  repeat' first
    | (transport_carrier_head encryptIterObserved; exact encryptIter h)
    | solve | transport_scheduler_native
    | transport_carrier_product_step
  all_goals exact product_throw _

theorem iteration (h : WorkerSafe extra origin replay hooks) (act : Activation) :
    ProductSafe extra origin replay (iterationObserved hooks act) := by
  unfold iterationObserved
  repeat' first
    | (transport_carrier_head encryptIterObserved; exact encryptIter h)
    | (transport_carrier_head decryptIterObserved; exact decryptIter h)
    | (transport_carrier_head receiveIterObserved; exact receiveIter h)
    | (transport_carrier_head txIterObserved; exact txIter h _)
    | (transport_carrier_head cryptAheadObserved; exact cryptAhead h _)
    | solve | transport_scheduler_native
    | transport_carrier_product_step

theorem schedule (h : WorkerSafe extra origin replay hooks) (stack : Option Worker) :
    ProductSafe extra origin replay (scheduleObserved hooks stack) := by
  apply SourceScheduler.schedule_preserves (I := ProductInv extra origin replay)
    (fun _ _ hi => hi.2) product_store
  · intro pid
    exact product_wg _ (modifyDev_rx _ (fun _ => rfl) (fun _ => rfl))
  · exact iteration h
  · exact softirq h.napi

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
