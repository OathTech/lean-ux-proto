import Leanux.Proofs.WG.AllowedIps.RoutingEnvTimersFrames
import Leanux.Proofs.Framing.EnvOperations
import Leanux.Proofs.WG.Environment.BatchSource

/-! Original environment ingress, exact flood and batch submission retain
routing at normal endpoints. Concrete nested scheduling closes the full receive
worker. Saved device scalars and lists need no current-device equality premise;
all actual getters, record failures and finite exhaustion remain unchanged. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem wgKernel_routing (a : Leanux.M α) (ha : SameView (fun w : World => wgStoreView w.wg) a) :
    SameView (fun w : World => routingView w.wg) a :=
  ha.of_factor (fun k : WGStoreView => k.dev.map routingState) (fun w : World => routingView w.wg) (fun _ => rfl)

private theorem product_store_routing (a : Leanux.M α) (ha : SameProductStore a) :
    SameView (fun w : World => routingView w.wg) a :=
  ha.of_factor (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg) (fun _ => rfl)

private theorem workerLoop_routing (worker : Worker) (pid : Option Nat)
    (step : Leanux.M Bool) (afterItem : Leanux.M Unit) (bound : Nat) (drained : String)
    (hs : ProductRetainsRoutingCall step) (ha : ProductRetainsRoutingCall afterItem) :
    ProductRetainsRoutingCall (workerLoop worker pid step afterItem bound drained) := by
  have hafter : ProductRetainsRoutingCall (do afterItem; pure false) := by
    intro s
    have h := RetainsRoutingCall.wp ha s
    exact hoare_consequence (preserves_bind h (fun _ => preserves_pure false))
      (fun w he => by
        change RetainsRouting s (routingView w.wg)
        change routingView w.wg = s at he
        rw [he]
        exact RetainsRouting.refl _) (fun _ _ h => h)
  intro s
  let P := RetainsRouting s
  have hi := RetainsRoutingCall.wp (workerIter_routing worker pid step _ hs hafter) s
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have choose {α : Type} (condition : Prop) [Decidable condition] (yes no : Leanux.M α)
      (hy : condition → Preserves (fun w : World => P (routingView w.wg)) yes)
      (hn : ¬condition → Preserves (fun w : World => P (routingView w.wg)) no) :
      Preserves (fun w : World => P (routingView w.wg)) (if condition then yes else no) := by
    split
    · apply hy; assumption
    · apply hn; assumption
  have loop {β : Type} (range : Std.Legacy.Range) (initial : β)
      (body : Nat → β → Leanux.M (ForInStep β))
      (hb : ∀ i b, Preserves (fun w : World => P (routingView w.wg)) (body i b)) :
      Preserves (fun w : World => P (routingView w.wg)) (forIn range initial body) := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    exact list_view_spec (fun w : World => routingView w.wg) P _ _ _ hb
  have main : Preserves (fun w : World => P (routingView w.wg))
      (workerLoop worker pid step afterItem bound drained) := by
    unfold workerLoop
    repeat' first
      | (routing_worker_head workerIter; exact hi)
      | (routing_worker_head invariant; exact ambient (AmbientM.invariant _))
      | routing_worker_join
      | routing_worker_join_use
      | (routing_worker_head Pure.pure; exact preserves_pure _)
      | (routing_worker_head Bind.bind; apply preserves_bind)
      | (routing_worker_head ForIn.forIn; apply loop)
      | (routing_worker_head ite; apply choose)
      | maintenance_intro
      | routing_worker_reduce
      | routing_worker_match
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w.wg)
    change routingView w.wg = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem handshakeReceiveWorker_routing :
    ProductRetainsRoutingCall (handshakeReceiveWorker (Env.nestedResched .receiveWorker)) :=
  workerLoop_routing _ _ _ _ _ _ receiveStep_routing.liftWG (nestedResched_routing .receiveWorker)

theorem xmitMulticastLoop_routing (family addr : Nat) :
    SameView (fun w : World => routingView w.wg) (Env.xmitMulticastLoop family addr) := by
  intro s
  change Preserves (fun w : World => routingView w.wg = s) (Env.xmitMulticastLoop family addr)
  have loopback := (sameView_liftWG (fun w : World => routingView w.wg) routingView _
    (routing_kernel _ (Queues.loopbackSend_kernel [] true)) (fun _ _ _ h => h)).wp (fun t => t = s)
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => routingView w.wg = s) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ h => h)
  unfold Env.xmitMulticastLoop
  split
  · exact loopback
  · split
    · exact ambient (AmbientM.unsupported _)
    · exact preserves_pure _

theorem inject_routing (family port : Nat) (msg : List UInt8) (tos : Nat)
    (ll : Bool) (dest : Nat) : ProductRetainsRoutingCall (Env.inject family port msg tos ll dest) := by
  intro s
  let P := RetainsRouting s
  have main : Preserves (fun w : World => P (routingView w.wg)) (Env.inject family port msg tos ll dest) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    have fixture : Preserves (fun w : World => P (routingView w.wg)) Env.fixtureSend :=
      productAmbient_spec (AmbientM.skipCut _) (fun w : World => P (routingView w.wg))
        (fun _ _ h => h)
    have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have edit := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have choose {α : Type} (condition : Prop) [Decidable condition] (yes no : Leanux.M α)
        (hy : condition → Preserves (fun w : World => P (routingView w.wg)) yes)
        (hn : ¬condition → Preserves (fun w : World => P (routingView w.wg)) no) :
        Preserves (fun w : World => P (routingView w.wg)) (if condition then yes else no) := by
      split
      · apply hy; assumption
      · apply hn; assumption
    have loop {β : Type} (range : Std.Legacy.Range) (initial : β)
        (body : Nat → β → Leanux.M (ForInStep β))
        (hb : ∀ i b, Preserves (fun w : World => P (routingView w.wg)) (body i b)) :
        Preserves (fun w : World => P (routingView w.wg)) (forIn range initial body) := by
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      exact list_view_spec (fun w : World => routingView w.wg) P _ _ _ hb
    have readRouting : Preserves (fun w : World => P (routingView w.wg)) (getRouting : Leanux.M _) := by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
      exact hi
    have readEnv : Preserves (fun w : World => P (routingView w.wg)) getEnv := by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
      exact hi
    have routing {α : Type} (a : Net.M α) :=
      productRouting_spec a (fun store => P (store.2.2.2.dev.map routingState))
    have native {α : Type} (a : WG.M α) (ha : SameView routingView a) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      (sameView_liftWG (fun w : World => routingView w.wg) routingView a ha
        (fun _ _ _ h => h)).wp P
    have list {α β : Type} (xs : List α) (initial : β)
        (body : α → β → Leanux.M (ForInStep β))
        (hb : ∀ x b, Preserves (fun w : World => P (routingView w.wg)) (body x b)) :
        Preserves (fun w : World => P (routingView w.wg)) (forIn xs initial body) :=
      list_view_spec (m := Except Stop) (fun w : World => routingView w.wg) P xs initial body hb
    have discardSpec {α : Type} (a : Leanux.M α)
        (ha : Preserves (fun w : World => P (routingView w.wg)) a) :
        Preserves (fun w : World => P (routingView w.wg)) (discard a) :=
      discard_view_spec (fun w : World => routingView w.wg) P a ha
    have peek := peekNextSite_sameKernel.of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w : World => routingView w.wg) (fun _ => rfl) |>.wp P
    have notPending (pid : PeerId) := native _ (requireNotPending_routing pid "receiving while a handshake is queued")
    have sender := (product_store_routing _ (senderSource_sameKernel family dest tos ll)).wp P
    have worker (src : SkbSource) := RetainsRoutingCall.wp
      (runWorker_routing .netRx _ (wgReceive_routing msg src).liftWG) s
    have crypt := RetainsRoutingCall.wp runCryptWorkers_routing s
    have drained (queues : List Bool) := (requireDrained_routing "the datagram queued" queues).wp P
    unfold Env.inject
    repeat' first
      | (routing_worker_head requireNotPending; exact notPending _)
      | (routing_worker_head Env.senderSource; exact sender)
      | (routing_worker_head Env.runWorker; exact worker _)
      | (routing_worker_head Env.runCryptWorkers; exact crypt)
      | (routing_worker_head Env.requireDrained; exact drained _)
      | routing_worker_join
      | routing_worker_join_use
      | (routing_worker_head getRouting; exact readRouting)
      | (routing_worker_head getEnv; exact readEnv)
      | (routing_worker_head Net.routeOutput4; exact routing (Net.routeOutput4 _ _))
      | (routing_worker_head Net.routeLookup; exact routing (Net.routeLookup _ _ _))
      | (routing_worker_head Net.neighbourClassify; exact routing (Net.neighbourClassify _))
      | (routing_worker_head Net.Fib.inSocketNs;
          exact routing (Net.Fib.inSocketNs _))
      | (routing_worker_head Env.fixtureSend; exact fixture)
      | (routing_worker_head Env.peekNextSite; exact peek)
      | (routing_worker_head getWG; exact readWG)
      | (routing_worker_head getDev; exact dev)
      | (routing_worker_head modifyWG; exact edit _ (fun _ => rfl))
      | (routing_worker_head getAmbient; exact ambient (get : AmbientM Ambient))
      | (routing_worker_head modifyAmbient; exact ambient (modify _ : AmbientM Unit))
      | (routing_worker_head invariant; exact ambient (AmbientM.invariant _))
      | (routing_worker_head unsupported; exact ambient (AmbientM.unsupported _))
      | (routing_worker_head recordBudget; exact ambient AmbientM.recordBudget)
      | (routing_worker_head peekUnit; exact ambient (AmbientM.peekUnit _))
      | (routing_worker_head peekSiteU64; exact ambient (AmbientM.peekSiteU64 _))
      | (routing_worker_head resolveUnit; exact ambient (AmbientM.resolveUnit _ _ _))
      | (routing_worker_head budgetExhausted; exact ambient (AmbientM.budgetExhausted _))
      | (routing_worker_head Functor.discard; apply discardSpec)
      | (routing_worker_head throw; exact hoare_throw _)
      | (routing_worker_head MonadExceptOf.throw; exact hoare_throw _)
      | (routing_worker_head Pure.pure; exact preserves_pure _)
      | (routing_worker_head Bind.bind; apply preserves_bind)
      | (routing_worker_head ForIn.forIn; first | apply loop | apply list)
      | (routing_worker_head ite; apply choose)
      | maintenance_intro
      | routing_worker_reduce
      | routing_worker_match
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w.wg)
    change routingView w.wg = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem afterBatch_routing : ProductRetainsRoutingCall Env.afterBatch := by
  intro s
  let P := RetainsRouting s
  have main : Preserves (fun w : World => P (routingView w.wg)) (Env.afterBatch) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    have fixture : Preserves (fun w : World => P (routingView w.wg)) Env.fixtureSend :=
      productAmbient_spec (AmbientM.skipCut _) (fun w : World => P (routingView w.wg))
        (fun _ _ h => h)
    have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have edit := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have choose {α : Type} (condition : Prop) [Decidable condition] (yes no : Leanux.M α)
        (hy : condition → Preserves (fun w : World => P (routingView w.wg)) yes)
        (hn : ¬condition → Preserves (fun w : World => P (routingView w.wg)) no) :
        Preserves (fun w : World => P (routingView w.wg)) (if condition then yes else no) := by
      split
      · apply hy; assumption
      · apply hn; assumption
    have loop {β : Type} (range : Std.Legacy.Range) (initial : β)
        (body : Nat → β → Leanux.M (ForInStep β))
        (hb : ∀ i b, Preserves (fun w : World => P (routingView w.wg)) (body i b)) :
        Preserves (fun w : World => P (routingView w.wg)) (forIn range initial body) := by
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      exact list_view_spec (fun w : World => routingView w.wg) P _ _ _ hb
    have readRouting : Preserves (fun w : World => P (routingView w.wg)) (getRouting : Leanux.M _) := by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
      exact hi
    have readEnv : Preserves (fun w : World => P (routingView w.wg)) getEnv := by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
      exact hi
    have routing {α : Type} (a : Net.M α) :=
      productRouting_spec a (fun store => P (store.2.2.2.dev.map routingState))
    have native {α : Type} (a : WG.M α) (ha : SameView routingView a) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      (sameView_liftWG (fun w : World => routingView w.wg) routingView a ha
        (fun _ _ _ h => h)).wp P
    have list {α β : Type} (xs : List α) (initial : β)
        (body : α → β → Leanux.M (ForInStep β))
        (hb : ∀ x b, Preserves (fun w : World => P (routingView w.wg)) (body x b)) :
        Preserves (fun w : World => P (routingView w.wg)) (forIn xs initial body) :=
      list_view_spec (m := Except Stop) (fun w : World => routingView w.wg) P xs initial body hb
    have discardSpec {α : Type} (a : Leanux.M α)
        (ha : Preserves (fun w : World => P (routingView w.wg)) a) :
        Preserves (fun w : World => P (routingView w.wg)) (discard a) :=
      discard_view_spec (fun w : World => routingView w.wg) P a ha
    have peek := peekNextSite_sameKernel.of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w : World => routingView w.wg) (fun _ => rfl) |>.wp P
    have crypt := RetainsRoutingCall.wp runCryptWorkers_routing s
    have send := RetainsRoutingCall.wp runSendWorkers_routing s
    have worker := RetainsRoutingCall.wp runOneSendWorker_routing s
    have schedule := RetainsRoutingCall.wp (schedule_routing none) s
    have drained (queues : List Bool) := (requireDrained_routing "the batch queued" queues).wp P
    have deliver := deliverSent_routing.wp P
    unfold Env.afterBatch
    repeat' first
      | (routing_worker_head Env.runCryptWorkers; exact crypt)
      | (routing_worker_head Env.runSendWorkers; exact send)
      | (routing_worker_head Env.runOneSendWorker; exact worker)
      | (routing_worker_head Env.schedule; exact schedule)
      | (routing_worker_head Env.requireDrained; exact drained _)
      | (routing_worker_head Env.deliverSent; exact deliver)
      | routing_worker_join
      | routing_worker_join_use
      | (routing_worker_head getRouting; exact readRouting)
      | (routing_worker_head getEnv; exact readEnv)
      | (routing_worker_head Net.routeOutput4; exact routing (Net.routeOutput4 _ _))
      | (routing_worker_head Net.routeLookup; exact routing (Net.routeLookup _ _ _))
      | (routing_worker_head Net.neighbourClassify; exact routing (Net.neighbourClassify _))
      | (routing_worker_head Net.Fib.inSocketNs;
          exact routing (Net.Fib.inSocketNs _))
      | (routing_worker_head Env.fixtureSend; exact fixture)
      | (routing_worker_head Env.peekNextSite; exact peek)
      | (routing_worker_head getWG; exact readWG)
      | (routing_worker_head getDev; exact dev)
      | (routing_worker_head modifyWG; exact edit _ (fun _ => rfl))
      | (routing_worker_head getAmbient; exact ambient (get : AmbientM Ambient))
      | (routing_worker_head modifyAmbient; exact ambient (modify _ : AmbientM Unit))
      | (routing_worker_head invariant; exact ambient (AmbientM.invariant _))
      | (routing_worker_head unsupported; exact ambient (AmbientM.unsupported _))
      | (routing_worker_head recordBudget; exact ambient AmbientM.recordBudget)
      | (routing_worker_head peekUnit; exact ambient (AmbientM.peekUnit _))
      | (routing_worker_head peekSiteU64; exact ambient (AmbientM.peekSiteU64 _))
      | (routing_worker_head resolveUnit; exact ambient (AmbientM.resolveUnit _ _ _))
      | (routing_worker_head budgetExhausted; exact ambient (AmbientM.budgetExhausted _))
      | (routing_worker_head Functor.discard; apply discardSpec)
      | (routing_worker_head throw; exact hoare_throw _)
      | (routing_worker_head MonadExceptOf.throw; exact hoare_throw _)
      | (routing_worker_head Pure.pure; exact preserves_pure _)
      | (routing_worker_head Bind.bind; apply preserves_bind)
      | (routing_worker_head ForIn.forIn; first | apply loop | apply list)
      | (routing_worker_head ite; apply choose)
      | maintenance_intro
      | routing_worker_reduce
      | routing_worker_match
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w.wg)
    change routingView w.wg = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem flood_routing (count port family : Nat) (messages : List (List UInt8)) :
    ProductRetainsRoutingCall (Env.flood count port family messages) := by
  intro s
  let P := RetainsRouting s
  have main : Preserves (fun w : World => P (routingView w.wg)) (Env.flood count port family messages) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    have fixture : Preserves (fun w : World => P (routingView w.wg)) Env.fixtureSend :=
      productAmbient_spec (AmbientM.skipCut _) (fun w : World => P (routingView w.wg))
        (fun _ _ h => h)
    have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have edit := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have choose {α : Type} (condition : Prop) [Decidable condition] (yes no : Leanux.M α)
        (hy : condition → Preserves (fun w : World => P (routingView w.wg)) yes)
        (hn : ¬condition → Preserves (fun w : World => P (routingView w.wg)) no) :
        Preserves (fun w : World => P (routingView w.wg)) (if condition then yes else no) := by
      split
      · apply hy; assumption
      · apply hn; assumption
    have loop {β : Type} (range : Std.Legacy.Range) (initial : β)
        (body : Nat → β → Leanux.M (ForInStep β))
        (hb : ∀ i b, Preserves (fun w : World => P (routingView w.wg)) (body i b)) :
        Preserves (fun w : World => P (routingView w.wg)) (forIn range initial body) := by
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      exact list_view_spec (fun w : World => routingView w.wg) P _ _ _ hb
    have readRouting : Preserves (fun w : World => P (routingView w.wg)) (getRouting : Leanux.M _) := by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
      exact hi
    have readEnv : Preserves (fun w : World => P (routingView w.wg)) getEnv := by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
      exact hi
    have routing {α : Type} (a : Net.M α) :=
      productRouting_spec a (fun store => P (store.2.2.2.dev.map routingState))
    have native {α : Type} (a : WG.M α) (ha : SameView routingView a) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      (sameView_liftWG (fun w : World => routingView w.wg) routingView a ha
        (fun _ _ _ h => h)).wp P
    have list {α β : Type} (xs : List α) (initial : β)
        (body : α → β → Leanux.M (ForInStep β))
        (hb : ∀ x b, Preserves (fun w : World => P (routingView w.wg)) (body x b)) :
        Preserves (fun w : World => P (routingView w.wg)) (forIn xs initial body) :=
      list_view_spec (m := Except Stop) (fun w : World => routingView w.wg) P xs initial body hb
    have discardSpec {α : Type} (a : Leanux.M α)
        (ha : Preserves (fun w : World => P (routingView w.wg)) a) :
        Preserves (fun w : World => P (routingView w.wg)) (discard a) :=
      discard_view_spec (fun w : World => routingView w.wg) P a ha
    have peek := peekNextSite_sameKernel.of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w : World => routingView w.wg) (fun _ => rfl) |>.wp P
    have notPending (pid : PeerId) := native _ (requireNotPending_routing pid "a flood while a handshake is queued")
    have sender := (product_store_routing _ (senderSource_sameKernel family 0 0 false)).wp P
    have receive (msg : List UInt8) (src : SkbSource) :
        ProductRetainsRoutingCall (Env.runWorker .netRx (do
          monadLift (wgReceive msg src)
          Env.pollScheduledInline)) := by
      apply runWorker_routing
      intro t
      have hr := RetainsRoutingCall.wp (wgReceive_routing msg src).liftWG t
      have hp := RetainsRoutingCall.wp pollScheduledInline_routing t
      exact hoare_consequence (preserves_bind hr (fun _ => hp))
        (fun w he => by
          change RetainsRouting t (routingView w.wg)
          change routingView w.wg = t at he
          rw [he]
          exact RetainsRouting.refl _) (fun _ _ h => h)
    have receiveSpec (msg : List UInt8) (src : SkbSource) := RetainsRoutingCall.wp (receive msg src) s
    have after := RetainsRoutingCall.wp afterBatch_routing s
    have drained (queues : List Bool) := (requireDrained_routing "the flood queued" queues).wp P
    unfold Env.flood
    repeat' first
      | (routing_worker_head requireNotPending; exact notPending _)
      | (routing_worker_head Env.senderSource; exact sender)
      | (routing_worker_head Env.runWorker; exact receiveSpec _ _)
      | (routing_worker_head Env.afterBatch; exact after)
      | (routing_worker_head Env.requireDrained; exact drained _)
      | routing_worker_join
      | routing_worker_join_use
      | (routing_worker_head getRouting; exact readRouting)
      | (routing_worker_head getEnv; exact readEnv)
      | (routing_worker_head Net.routeOutput4; exact routing (Net.routeOutput4 _ _))
      | (routing_worker_head Net.routeLookup; exact routing (Net.routeLookup _ _ _))
      | (routing_worker_head Net.neighbourClassify; exact routing (Net.neighbourClassify _))
      | (routing_worker_head Net.Fib.inSocketNs;
          exact routing (Net.Fib.inSocketNs _))
      | (routing_worker_head Env.fixtureSend; exact fixture)
      | (routing_worker_head Env.peekNextSite; exact peek)
      | (routing_worker_head getWG; exact readWG)
      | (routing_worker_head getDev; exact dev)
      | (routing_worker_head modifyWG; exact edit _ (fun _ => rfl))
      | (routing_worker_head getAmbient; exact ambient (get : AmbientM Ambient))
      | (routing_worker_head modifyAmbient; exact ambient (modify _ : AmbientM Unit))
      | (routing_worker_head invariant; exact ambient (AmbientM.invariant _))
      | (routing_worker_head unsupported; exact ambient (AmbientM.unsupported _))
      | (routing_worker_head recordBudget; exact ambient AmbientM.recordBudget)
      | (routing_worker_head peekUnit; exact ambient (AmbientM.peekUnit _))
      | (routing_worker_head peekSiteU64; exact ambient (AmbientM.peekSiteU64 _))
      | (routing_worker_head resolveUnit; exact ambient (AmbientM.resolveUnit _ _ _))
      | (routing_worker_head budgetExhausted; exact ambient (AmbientM.budgetExhausted _))
      | (routing_worker_head Functor.discard; apply discardSpec)
      | (routing_worker_head throw; exact hoare_throw _)
      | (routing_worker_head MonadExceptOf.throw; exact hoare_throw _)
      | (routing_worker_head Pure.pure; exact preserves_pure _)
      | (routing_worker_head Bind.bind; apply preserves_bind)
      | (routing_worker_head ForIn.forIn; first | apply loop | apply list)
      | (routing_worker_head ite; apply choose)
      | maintenance_intro
      | routing_worker_reduce
      | routing_worker_match
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w.wg)
    change routingView w.wg = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem batchItem_routing (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductRetainsRoutingCall (Environment.batchItemSource d cqes item) := by
  intro s
  let P := RetainsRouting s
  have main : Preserves (fun w : World => P (routingView w.wg)) (Environment.batchItemSource d cqes item) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    have fixture : Preserves (fun w : World => P (routingView w.wg)) Env.fixtureSend :=
      productAmbient_spec (AmbientM.skipCut _) (fun w : World => P (routingView w.wg))
        (fun _ _ h => h)
    have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have edit := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have choose {α : Type} (condition : Prop) [Decidable condition] (yes no : Leanux.M α)
        (hy : condition → Preserves (fun w : World => P (routingView w.wg)) yes)
        (hn : ¬condition → Preserves (fun w : World => P (routingView w.wg)) no) :
        Preserves (fun w : World => P (routingView w.wg)) (if condition then yes else no) := by
      split
      · apply hy; assumption
      · apply hn; assumption
    have loop {β : Type} (range : Std.Legacy.Range) (initial : β)
        (body : Nat → β → Leanux.M (ForInStep β))
        (hb : ∀ i b, Preserves (fun w : World => P (routingView w.wg)) (body i b)) :
        Preserves (fun w : World => P (routingView w.wg)) (forIn range initial body) := by
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      exact list_view_spec (fun w : World => routingView w.wg) P _ _ _ hb
    have readRouting : Preserves (fun w : World => P (routingView w.wg)) (getRouting : Leanux.M _) := by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
      exact hi
    have readEnv : Preserves (fun w : World => P (routingView w.wg)) getEnv := by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
      exact hi
    have routing {α : Type} (a : Net.M α) :=
      productRouting_spec a (fun store => P (store.2.2.2.dev.map routingState))
    have native {α : Type} (a : WG.M α) (ha : SameView routingView a) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      (sameView_liftWG (fun w : World => routingView w.wg) routingView a ha
        (fun _ _ _ h => h)).wp P
    have list {α β : Type} (xs : List α) (initial : β)
        (body : α → β → Leanux.M (ForInStep β))
        (hb : ∀ x b, Preserves (fun w : World => P (routingView w.wg)) (body x b)) :
        Preserves (fun w : World => P (routingView w.wg)) (forIn xs initial body) :=
      list_view_spec (m := Except Stop) (fun w : World => routingView w.wg) P xs initial body hb
    have discardSpec {α : Type} (a : Leanux.M α)
        (ha : Preserves (fun w : World => P (routingView w.wg)) a) :
        Preserves (fun w : World => P (routingView w.wg)) (discard a) :=
      discard_view_spec (fun w : World => routingView w.wg) P a ha
    have peek := peekNextSite_sameKernel.of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w : World => routingView w.wg) (fun _ => rfl) |>.wp P
    have sender (family : Nat) := (product_store_routing _ (senderSource_sameKernel family 0 0 false)).wp P
    have receive (msg : List UInt8) (src : SkbSource) :
        ProductRetainsRoutingCall (Env.runWorker .netRx (do
          monadLift (wgReceive msg src)
          Env.pollScheduledInline)) := by
      apply runWorker_routing
      intro t
      have hr := RetainsRoutingCall.wp (wgReceive_routing msg src).liftWG t
      have hp := RetainsRoutingCall.wp pollScheduledInline_routing t
      exact hoare_consequence (preserves_bind hr (fun _ => hp))
        (fun w he => by
          change RetainsRouting t (routingView w.wg)
          change routingView w.wg = t at he
          rw [he]
          exact RetainsRouting.refl _) (fun _ _ h => h)
    have receiveSpec (msg : List UInt8) (src : SkbSource) := RetainsRoutingCall.wp (receive msg src) s
    have packets (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :=
      (product_store_routing _ (xmitPackets_sameKernel family addr payload opts)).wp P
    have multicast (family addr : Nat) := (xmitMulticastLoop_routing family addr).wp P
    have xmit (family addr : Nat) (pkts : List Packet) (mtu : Nat) :=
      RetainsRoutingCall.wp (wgXmit_routing family addr pkts mtu).liftWG s
    unfold Environment.batchItemSource
    repeat' first
      | (routing_worker_head Env.senderSource; exact sender _)
      | (routing_worker_head Env.runWorker; exact receiveSpec _ _)
      | (routing_worker_head Env.xmitPackets; exact packets _ _ _ _)
      | (routing_worker_head Env.xmitMulticastLoop; exact multicast _ _)
      | (routing_worker_head wgXmit; exact xmit _ _ _ _)
      | routing_worker_join
      | routing_worker_join_use
      | (routing_worker_head getRouting; exact readRouting)
      | (routing_worker_head getEnv; exact readEnv)
      | (routing_worker_head Net.routeOutput4; exact routing (Net.routeOutput4 _ _))
      | (routing_worker_head Net.routeLookup; exact routing (Net.routeLookup _ _ _))
      | (routing_worker_head Net.neighbourClassify; exact routing (Net.neighbourClassify _))
      | (routing_worker_head Net.Fib.inSocketNs;
          exact routing (Net.Fib.inSocketNs _))
      | (routing_worker_head Env.fixtureSend; exact fixture)
      | (routing_worker_head Env.peekNextSite; exact peek)
      | (routing_worker_head getWG; exact readWG)
      | (routing_worker_head getDev; exact dev)
      | (routing_worker_head modifyWG; exact edit _ (fun _ => rfl))
      | (routing_worker_head getAmbient; exact ambient (get : AmbientM Ambient))
      | (routing_worker_head modifyAmbient; exact ambient (modify _ : AmbientM Unit))
      | (routing_worker_head invariant; exact ambient (AmbientM.invariant _))
      | (routing_worker_head unsupported; exact ambient (AmbientM.unsupported _))
      | (routing_worker_head recordBudget; exact ambient AmbientM.recordBudget)
      | (routing_worker_head peekUnit; exact ambient (AmbientM.peekUnit _))
      | (routing_worker_head peekSiteU64; exact ambient (AmbientM.peekSiteU64 _))
      | (routing_worker_head resolveUnit; exact ambient (AmbientM.resolveUnit _ _ _))
      | (routing_worker_head budgetExhausted; exact ambient (AmbientM.budgetExhausted _))
      | (routing_worker_head Functor.discard; apply discardSpec)
      | (routing_worker_head throw; exact hoare_throw _)
      | (routing_worker_head MonadExceptOf.throw; exact hoare_throw _)
      | (routing_worker_head Pure.pure; exact preserves_pure _)
      | (routing_worker_head Bind.bind; apply preserves_bind)
      | (routing_worker_head ForIn.forIn; first | apply loop | apply list)
      | (routing_worker_head ite; apply choose)
      | maintenance_intro
      | routing_worker_reduce
      | routing_worker_match
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w.wg)
    change routingView w.wg = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem batch_routing (items : List Env.BatchItem) : ProductRetainsRoutingCall (Env.batch items) := by
  rw [← Environment.batchSource_eq]
  intro s
  let P := RetainsRouting s
  have main : Preserves (fun w : World => P (routingView w.wg)) (Environment.batchSource items) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    have fixture : Preserves (fun w : World => P (routingView w.wg)) Env.fixtureSend :=
      productAmbient_spec (AmbientM.skipCut _) (fun w : World => P (routingView w.wg))
        (fun _ _ h => h)
    have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have edit := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have choose {α : Type} (condition : Prop) [Decidable condition] (yes no : Leanux.M α)
        (hy : condition → Preserves (fun w : World => P (routingView w.wg)) yes)
        (hn : ¬condition → Preserves (fun w : World => P (routingView w.wg)) no) :
        Preserves (fun w : World => P (routingView w.wg)) (if condition then yes else no) := by
      split
      · apply hy; assumption
      · apply hn; assumption
    have loop {β : Type} (range : Std.Legacy.Range) (initial : β)
        (body : Nat → β → Leanux.M (ForInStep β))
        (hb : ∀ i b, Preserves (fun w : World => P (routingView w.wg)) (body i b)) :
        Preserves (fun w : World => P (routingView w.wg)) (forIn range initial body) := by
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      exact list_view_spec (fun w : World => routingView w.wg) P _ _ _ hb
    have readRouting : Preserves (fun w : World => P (routingView w.wg)) (getRouting : Leanux.M _) := by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
      exact hi
    have readEnv : Preserves (fun w : World => P (routingView w.wg)) getEnv := by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
      exact hi
    have routing {α : Type} (a : Net.M α) :=
      productRouting_spec a (fun store => P (store.2.2.2.dev.map routingState))
    have native {α : Type} (a : WG.M α) (ha : SameView routingView a) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      (sameView_liftWG (fun w : World => routingView w.wg) routingView a ha
        (fun _ _ _ h => h)).wp P
    have list {α β : Type} (xs : List α) (initial : β)
        (body : α → β → Leanux.M (ForInStep β))
        (hb : ∀ x b, Preserves (fun w : World => P (routingView w.wg)) (body x b)) :
        Preserves (fun w : World => P (routingView w.wg)) (forIn xs initial body) :=
      list_view_spec (m := Except Stop) (fun w : World => routingView w.wg) P xs initial body hb
    have discardSpec {α : Type} (a : Leanux.M α)
        (ha : Preserves (fun w : World => P (routingView w.wg)) a) :
        Preserves (fun w : World => P (routingView w.wg)) (discard a) :=
      discard_view_spec (fun w : World => routingView w.wg) P a ha
    have peek := peekNextSite_sameKernel.of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w : World => routingView w.wg) (fun _ => rfl) |>.wp P
    have notPending (pid : PeerId) := native _ (requireNotPending_routing pid "a batch while a handshake is queued")
    have item (d : Device) (cqes : List Int) (item : Env.BatchItem) := RetainsRoutingCall.wp (batchItem_routing d cqes item) s
    have after := RetainsRoutingCall.wp afterBatch_routing s
    unfold Environment.batchSource
    repeat' first
      | (routing_worker_head requireNotPending; exact notPending _)
      | (routing_worker_head Environment.batchItemSource; exact item _ _ _)
      | (routing_worker_head Env.afterBatch; exact after)
      | routing_worker_join
      | routing_worker_join_use
      | (routing_worker_head getRouting; exact readRouting)
      | (routing_worker_head getEnv; exact readEnv)
      | (routing_worker_head Net.routeOutput4; exact routing (Net.routeOutput4 _ _))
      | (routing_worker_head Net.routeLookup; exact routing (Net.routeLookup _ _ _))
      | (routing_worker_head Net.neighbourClassify; exact routing (Net.neighbourClassify _))
      | (routing_worker_head Net.Fib.inSocketNs;
          exact routing (Net.Fib.inSocketNs _))
      | (routing_worker_head Env.fixtureSend; exact fixture)
      | (routing_worker_head Env.peekNextSite; exact peek)
      | (routing_worker_head getWG; exact readWG)
      | (routing_worker_head getDev; exact dev)
      | (routing_worker_head modifyWG; exact edit _ (fun _ => rfl))
      | (routing_worker_head getAmbient; exact ambient (get : AmbientM Ambient))
      | (routing_worker_head modifyAmbient; exact ambient (modify _ : AmbientM Unit))
      | (routing_worker_head invariant; exact ambient (AmbientM.invariant _))
      | (routing_worker_head unsupported; exact ambient (AmbientM.unsupported _))
      | (routing_worker_head recordBudget; exact ambient AmbientM.recordBudget)
      | (routing_worker_head peekUnit; exact ambient (AmbientM.peekUnit _))
      | (routing_worker_head peekSiteU64; exact ambient (AmbientM.peekSiteU64 _))
      | (routing_worker_head resolveUnit; exact ambient (AmbientM.resolveUnit _ _ _))
      | (routing_worker_head budgetExhausted; exact ambient (AmbientM.budgetExhausted _))
      | (routing_worker_head Functor.discard; apply discardSpec)
      | (routing_worker_head throw; exact hoare_throw _)
      | (routing_worker_head MonadExceptOf.throw; exact hoare_throw _)
      | (routing_worker_head Pure.pure; exact preserves_pure _)
      | (routing_worker_head Bind.bind; apply preserves_bind)
      | (routing_worker_head ForIn.forIn; first | apply loop | apply list)
      | (routing_worker_head ite; apply choose)
      | maintenance_intro
      | routing_worker_reduce
      | routing_worker_match
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w.wg)
    change routingView w.wg = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

end Leanux.Proofs.WG.AllowedIps
