import Leanux.Proofs.WG.Queues.SchedulerSource
import Leanux.Proofs.WG.Packets.OldProduct
import Leanux.Proofs.WG.AllowedIps.RoutingSchedulerFrames

/-! Invariant composition over the actual observed scheduler. Atomic contracts
name the original getter, saved queue update and copied-trial observers. Worker
and NAPI callbacks remain arbitrary product observers. -/
namespace Leanux.Proofs.WG.Queues.RxHistory.SchedulerSource
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes AllowedIps

/-- Only the actual atomic observer family used by these source bodies. -/
structure AtomContracts {E : Type} (I : List E → World → Prop) (S : List E → Prop)
    (old : {α : Type} → Obs α → PrefixM E α) : Prop where
  ambient : ∀ {α : Type} (a : AmbientM α),
    PrefixPreserves I S (old (mixed (liftPrefix (monadLift a : Leanux.M α))))
  stopped : ∀ {α : Type} (e : Stop), PrefixPreserves I S (old (mixed (throw e : PrefixM LifetimeEvent α)))
  peer : ∀ pid, PrefixPreserves I S (old (mixed (liftWGObserver (getPeerMixed pid))))
  packet : ∀ id, PrefixPreserves I S (old (mixed (liftWGObserver (getTxSkbPrefix id))))
  work : ∀ f : List PeerId → List PeerId, PrefixPreserves I S
    (old (mixed (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue})))))
  occupancy : ∀ a, PrefixPreserves I S (old (mixed (activationOccupancyPrefix a)))
  pending : ∀ next, PrefixPreserves I S (old (mixed (pendingNapiPrefix next)))
  hasWork : ∀ a, PrefixPreserves I S (old (mixed (activationHasWorkPrefix a)))
  trial : PrefixPreserves I S (old (audit consistentFilterAudit))

variable {E : Type} {I : List E → World → Prop} {S : List E → Prop}

private theorem product_routing (a : Leanux.M α) (frame : SameProductStore a) :
    ProductRetainsRoutingCall a :=
  ProjectedRetainsRoutingCall.of_same
    (frame.of_factor (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w : World => routingView w.wg) (fun _ => rfl))

/-- A semantic old-atom rule suffices: exact erasure and an actual source
routing-retention frame are required, not preservation of arbitrary observers. -/
theorem AtomContracts.of_routing (old : {α : Type} → Obs α → PrefixM E α)
    (ho : ∀ {α : Type} (g : Obs α) (a : Leanux.M α), Appends g → ErasesPrefix g a →
      ProductRetainsRoutingCall a → PrefixPreserves I S (old g)) : AtomContracts I S old := by
  have stored {α : Type} (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
      (erases : ErasesPrefix g a) (frame : SameProductStore a) :
      PrefixPreserves I S (old (mixed g)) :=
    ho _ a (Appends.focus _ _ _) (mixed_erases erases) (product_routing a frame)
  have native {α : Type} (g : WGPrefix LifetimeEvent α) (a : WG.M α)
      (erases : ErasesStatePrefix g a) (frame : SameView routingView a) :
      PrefixPreserves I S (old (mixed (liftWGObserver g))) :=
    ho _ (liftWG a) (Appends.focus _ _ _) (mixed_erases (liftWGObserver_erases erases))
      (RetainsRoutingCall.liftWG (ProjectedRetainsRoutingCall.of_same frame))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α a
    exact stored _ _ (erasesPrefix_lift _)
      (fun _ => productAmbient_spec a _ (fun _ _ hi => hi))
  · intro α e
    exact stored _ _ (erasesPrefix_throw e) (fun _ => hoare_throw e)
  · intro pid
    exact native _ _ (getPeerMixed_erases pid) (getPeer_routing pid)
  · intro id
    apply native _ _ (getTxSkbPrefix_erases id)
    intro initial
    apply hoare_liftSkb
    intro w d store hi hd
    simpa only [routingView, hd, Option.map_some, routingState] using hi
  · intro f
    exact native _ _ (erasesStatePrefix_lift _) (modifyDev_routing _ (fun _ => rfl))
  · intro a
    exact stored _ _ (activationOccupancyPrefix_erases a) (activationOccupancy_sameKernel a)
  · intro next
    exact stored _ _ (pendingNapiPrefix_erases next) (SourceScheduler.pendingNapi_kernel next)
  · intro a
    exact stored _ _ (activationHasWorkPrefix_erases a) (activationHasWork_sameKernel a)
  · apply ho _ _ (Appends.focus _ _ _) (audit_erases consistentFilterAudit_erases)
    apply product_routing
    exact (show SameProductStore getAmbient from fun initial =>
      productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ hi => hi)).bind
        (fun w => filterM_sameKernel productStoreView _ activationConsistent_sameKernel w.suspended)

private theorem raw (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (a : Leanux.M α) (frame : SameProductStore a) : PrefixPreserves I S (liftPrefix a) :=
  viewLiftPrefix_preserves productStoreView safe store frame

private theorem ambient (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (a : AmbientM α) : PrefixPreserves I S (liftPrefix (monadLift a : Leanux.M α)) :=
  raw safe store _ (fun _ => productAmbient_spec a _ (fun _ _ hi => hi))

/-- Inspect only the outer action and explicit source wrappers. The guard
selects an existing rule and never constructs a proof or changes a goal. -/
elab "scheduler_preserve_at " wanted:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``PrefixPreserves do Lean.throwError "not a preservation contract"
  let args := target.getAppArgs
  unless args.size > 0 do Lean.throwError "missing observer"
  let mut action := args.back!.consumeMData.headBeta
  if let .fvar f := action.getAppFn then
    if (← f.getDecl).userName.eraseMacroScopes.toString == "old" then
      let parts := action.getAppArgs
      unless parts.size > 0 do Lean.throwError "missing embedded observer"
      action := parts.back!.consumeMData.headBeta
  let expected := wanted.getId.eraseMacroScopes.toString
  for wrapper in [``mixed, ``audit, ``liftWGObserver, ``liftWGPrefix, ``liftPrefix, ``liftWG] do
    if action.isAppOf wrapper && expected != wrapper.toString && !wrapper.toString.endsWith ("." ++ expected) then
      let parts := action.getAppArgs
      unless parts.size > 0 do Lean.throwError "missing wrapped source"
      action := parts.back!.consumeMData.headBeta
  let actual ← match action.getAppFn with
    | .const n _ => pure n.toString
    | .fvar f => pure (← f.getDecl).userName.eraseMacroScopes.toString
    | _ => Lean.throwError "not a named source head"
  unless actual == expected || actual.endsWith ("." ++ expected) do
    Lean.throwError "different source head"

/-- The callback is the only committed encrypt execution. The old atoms retain
their concrete saved reads and temporary TX work-queue writes. -/
theorem cryptAhead_preserves (safe : ∀ h w, I h w → S h)
    (old : {α : Type} → Obs α → PrefixM E α) (atoms : AtomContracts I S old)
    (encrypt : PrefixM E IterResult) (he : PrefixPreserves I S encrypt) (pid : PeerId) :
    PrefixPreserves I S (cryptAheadWith old encrypt pid) := by
  unfold cryptAheadWith
  repeat' first
    | (scheduler_preserve_at encrypt; exact he)
    | (scheduler_preserve_at getPeerMixed; exact atoms.peer _)
    | (scheduler_preserve_at getTxSkbPrefix; exact atoms.packet _)
    | (scheduler_preserve_at modifyDev; first
        | exact atoms.work (fun q => q ++ [pid])
        | exact atoms.work (fun q => q.erase pid))
    | (scheduler_preserve_at throw; exact atoms.stopped _)
    | (scheduler_preserve_at getAmbient; exact atoms.ambient (get : AmbientM Ambient))
    | (scheduler_preserve_at peekHiddenSite; exact atoms.ambient AmbientM.peekHiddenSite)
    | (scheduler_preserve_at modifyAmbient; exact atoms.ambient (modify _ : AmbientM Unit))
    | (scheduler_preserve_at invariant; exact atoms.ambient (AmbientM.invariant _))
    | (scheduler_preserve_at Pure.pure; exact PrefixPreserves.pure safe _)
    | (scheduler_preserve_at Bind.bind; apply PrefixPreserves.bind)
    | maintenance_intro
    | (scheduler_preserve_at ite; split)
    | (scheduler_preserve_at dite; split)
    | (with_reducible split)
    | dsimp (config := {failIfUnchanged := true}) only

theorem iteration_preserves
    (old : {α : Type} → Obs α → PrefixM E α) (atoms : AtomContracts I S old)
    (encrypt : PrefixM E IterResult) (ahead : PeerId → PrefixM E Unit)
    (tx : PeerId → PrefixM E IterResult) (decrypt receive : PrefixM E IterResult)
    (he : PrefixPreserves I S encrypt) (ha : ∀ pid, PrefixPreserves I S (ahead pid))
    (ht : ∀ pid, PrefixPreserves I S (tx pid))
    (hd : PrefixPreserves I S decrypt) (hr : PrefixPreserves I S receive) (a : Activation) :
    PrefixPreserves I S (iterationWith old encrypt ahead tx decrypt receive a) := by
  unfold iterationWith
  repeat' first
    | (scheduler_preserve_at encrypt; exact he)
    | (scheduler_preserve_at ahead; exact ha _)
    | (scheduler_preserve_at tx; exact ht _)
    | (scheduler_preserve_at decrypt; exact hd)
    | (scheduler_preserve_at receive; exact hr)
    | (scheduler_preserve_at getAmbient; exact atoms.ambient (get : AmbientM Ambient))
    | (scheduler_preserve_at peekHiddenSite; exact atoms.ambient AmbientM.peekHiddenSite)
    | (scheduler_preserve_at modifyAmbient; exact atoms.ambient (modify _ : AmbientM Unit))
    | (scheduler_preserve_at invariant; exact atoms.ambient (AmbientM.invariant _))
    | (scheduler_preserve_at Bind.bind; apply PrefixPreserves.bind)
    | maintenance_intro
    | (scheduler_preserve_at ite; split)
    | (scheduler_preserve_at dite; split)
    | (with_reducible split)
    | dsimp (config := {failIfUnchanged := true}) only

macro "scheduler_raw_steps" safe:ident store:ident : tactic => `(tactic| first
  | (scheduler_preserve_at getDev; exact raw $safe $store _ (liftWG_sameProductStore getDev getDev_sameWGStore))
  | (scheduler_preserve_at hidden; exact ambient $safe $store (AmbientM.hidden _))
  | (scheduler_preserve_at invariant; exact ambient $safe $store (AmbientM.invariant _))
  | (scheduler_preserve_at unsupported; exact ambient $safe $store (AmbientM.unsupported _))
  | (scheduler_preserve_at getAmbient; exact ambient $safe $store (get : AmbientM Ambient))
  | (scheduler_preserve_at modifyAmbient; exact ambient $safe $store (modify _ : AmbientM Unit))
  | (scheduler_preserve_at peekUnit; exact ambient $safe $store (AmbientM.peekUnit _))
  | (scheduler_preserve_at resolveUnit; exact ambient $safe $store (AmbientM.resolveUnit _ _ _))
  | (scheduler_preserve_at peekHiddenSite; exact ambient $safe $store AmbientM.peekHiddenSite)
  | (scheduler_preserve_at recordBudget; exact ambient $safe $store AmbientM.recordBudget)
  | (scheduler_preserve_at budgetExhausted; exact ambient $safe $store (AmbientM.budgetExhausted _))
  | (scheduler_preserve_at Pure.pure; exact PrefixPreserves.pure $safe _)
  | (scheduler_preserve_at Bind.bind; apply PrefixPreserves.bind)
  | (scheduler_preserve_at ForIn.forIn; first
      | apply PrefixPreserves.range (State := World) _ _ _ $safe
      | apply PrefixPreserves.forIn _ _ _ $safe)
  | maintenance_intro
  | (scheduler_preserve_at ite; split)
  | (scheduler_preserve_at dite; split)
  | (with_reducible split)
  | dsimp (config := {failIfUnchanged := true}) only)

theorem run_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (old : {α : Type} → Obs α → PrefixM E α) (atoms : AtomContracts I S old)
    (iteration : Activation → PrefixM E IterResult)
    (hi : ∀ a, PrefixPreserves I S (iteration a)) (a : Activation) :
    PrefixPreserves I S (runWith old iteration a) := by
  unfold runWith
  repeat' first
    | (scheduler_preserve_at activationOccupancyPrefix; exact atoms.occupancy _)
    | (scheduler_preserve_at iteration; exact hi _)
    | scheduler_raw_steps safe store

theorem dispatch_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (old : {α : Type} → Obs α → PrefixM E α) (atoms : AtomContracts I S old)
    (run : Activation → PrefixM E Unit) (hr : ∀ a, PrefixPreserves I S (run a)) (worker : Worker) :
    PrefixPreserves I S (dispatchWith old run worker) := by
  unfold dispatchWith
  repeat' first
    | (scheduler_preserve_at modifyDev; exact atoms.work (fun q => q.erase _))
    | (scheduler_preserve_at run; exact hr _)
    | scheduler_raw_steps safe store

theorem schedule_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (old : {α : Type} → Obs α → PrefixM E α) (atoms : AtomContracts I S old)
    (dispatch : Worker → PrefixM E Bool) (run : Activation → PrefixM E Unit) (napi : PrefixM E Unit)
    (hd : ∀ worker, PrefixPreserves I S (dispatch worker))
    (hr : ∀ a, PrefixPreserves I S (run a)) (hn : PrefixPreserves I S napi) (stack : Option Worker) :
    PrefixPreserves I S (scheduleWith old dispatch run napi stack) := by
  unfold scheduleWith
  repeat' first
    | (scheduler_preserve_at pendingNapiPrefix; exact atoms.pending _)
    | (scheduler_preserve_at activationHasWorkPrefix; exact atoms.hasWork _)
    | (scheduler_preserve_at consistentFilterAudit; exact atoms.trial)
    | (scheduler_preserve_at dispatch; exact hd _)
    | (scheduler_preserve_at run; exact hr _)
    | (scheduler_preserve_at napi; exact hn)
    | scheduler_raw_steps safe store

theorem nested_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (schedule : Option Worker → PrefixM E Unit)
    (hs : ∀ stack, PrefixPreserves I S (schedule stack)) (worker : Worker) :
    PrefixPreserves I S (nestedWith schedule worker) := by
  unfold nestedWith
  apply PrefixPreserves.bind (raw safe store _ (condResched_sameKernel worker))
  intro ready
  split
  · exact hs _
  · exact PrefixPreserves.pure safe _

/-- The canonical old RX embedding discharges every actual atom contract.
It emits only old events; new transmit receipts must come from the explicitly
supplied committed callbacks. This is an entry-invariant preservation rule. -/
theorem transmit_atoms (initial : FlatTable × FlatTable) :
    AtomContracts (TransmitJoint.Inv initial) (TransmitJoint.Safe initial)
      (fun {_} g => TransmitJoint.oldProduct (RoutingJoint.rxAction g)) := by
  apply AtomContracts.of_routing
  intro α g a _ erases retained
  exact TransmitJoint.oldProduct_projected initial _ _ (Appends.focus _ _ _)
    (RoutingJoint.rxAction_routing erases)
    (global_completion_lift World.wg initial a retained)

end Leanux.Proofs.WG.Queues.RxHistory.SchedulerSource
