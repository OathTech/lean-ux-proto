import Leanux.Proofs.WG.AllowedIps.RoutingSendFrames
import Leanux.Proofs.WG.Queues.RxStackFrames
import Leanux.Proofs.WG.Lifetimes.SocketSend4

/-! Original socket-send routing frames. Existing socket source factors retain
all route, hidden-input and loopback branches; no successful-send premise is used. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem dstCacheGet_routing (pid : PeerId) (gen : Nat) : SameView routingView (dstCacheGet pid gen) := by
  intro initial
  let P := fun w : WGWorld => routingView w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (liftRouting a) :=
    hoare_liftRouting a P (fun _ _ hi => hi)
  have liftRoute {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) := routing a
  have routingRead : Preserves P (getRouting : WG.M Net.Routing) := routing ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  have dev : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp (fun v => v = initial)
  have edit (f : Device → Device) (hf : ∀ d, routingState (f d) = routingState d) :
      Preserves P (modifyDev f) := (modifyDev_routing f hf).wp (fun v => v = initial)
  have readBind {α : Type} (pid : PeerId) (f : Peer → WG.M α)
      (hf : ∀ p, initial.bind (fun view => view.lists pid) = some p.allowedipsList →
        Preserves P (f p)) : Preserves P (getPeer pid >>= f) := by
    apply hoare_bind _ _ (routing_getPeer (fun view => view = initial) pid)
    intro p
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' h hr
    have saved : (routingView w).bind (fun view => view.lists pid) = some p.allowedipsList := by
      simpa only [routingView, routingState, Option.bind_map, Function.comp_def] using h.2
    rw [h.1] at saved
    exact (hoare_iff_run_ambient _ _ _).mp (hf p saved) w ambient x v ambient' h.1 hr
  have knownSet (pid : PeerId) (p : Peer)
      (hp : initial.bind (fun view => view.lists pid) = some p.allowedipsList) :
      Preserves P (setPeer pid p) := by
    apply hoare_consequence (routing_setPeer (fun view => view = initial) pid p)
    · intro w h
      refine ⟨h, ?_⟩
      have current : (routingView w).bind (fun view => view.lists pid) = some p.allowedipsList := by
        rw [h]; exact hp
      simpa only [routingView, routingState, Option.bind_map, Function.comp_def] using current
    · exact fun _ _ h => h
  unfold dstCacheGet
  simp (config := { zeta := false }) only [getAmbient, hiddenJiffies, ]
  repeat' first
    | (run_tac Lean.Elab.Tactic.withMainContext do
        let target := (← Lean.Elab.Tactic.getMainTarget).consumeMData
        unless target.isAppOf ``Preserves && target.getAppArgs.size > 0 do
          throwError "not a routing preservation contract"
        let action := target.getAppArgs.back!.consumeMData.headBeta
        unless action.isAppOf ``Bind.bind && action.getAppArgs.size ≥ 2 do
          throwError "not a bind"
        let first := action.getAppArgs[action.getAppArgs.size - 2]!.consumeMData
        unless first.isAppOf ``getPeer do throwError "not a peer read"
       apply readBind
       intro p hp)
    | (rx_retention_head setPeer; apply knownSet; exact hp)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_lift_from Net.M; exact liftRoute _)
    | (rx_retention_head liftRouting; exact routing _)
    | (rx_retention_head getRouting; exact routingRead)
    | (rx_retention_head getDev; exact dev)
    | (rx_retention_head get; exact read)
    | (rx_retention_head MonadStateOf.get; exact read)
    | (rx_retention_head modifyDev; exact edit _ (fun _ => rfl))
    | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
    | rx_retention_step

theorem dstCacheSet_routing (pid : PeerId) (src gen dev : Nat) : SameView routingView (dstCacheSet pid src gen dev) := by
  intro initial
  unfold dstCacheSet
  apply hoare_bind _ _ (routing_getPeer (fun view => view = initial) pid)
  intro p
  exact routing_setPeer (fun view => view = initial) pid
    {p with dstCache := {p.dstCache with slot := some {src, gen, dev}}}

theorem tunnelXmit_routing (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    SameView routingView ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  intro initial
  let P := fun w : WGWorld => routingView w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (liftRouting a) :=
    hoare_liftRouting a P (fun _ _ hi => hi)
  have liftRoute {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) := routing a
  have routingRead : Preserves P (getRouting : WG.M Net.Routing) := routing ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  have dev : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp (fun v => v = initial)
  have edit (f : Device → Device) (hf : ∀ d, routingState (f d) = routingState d) :
      Preserves P (modifyDev f) := (modifyDev_routing f hf).wp (fun v => v = initial)
  have loopback := fun sites force => show Preserves P _ from
    (routing_kernel _ (Leanux.Proofs.WG.Queues.loopbackSend_kernel sites force)).wp (fun v => v = initial)
  have port := fun fam => show Preserves P _ from
    (routing_kernel _ (socketPort_sameStore fam)).wp (fun v => v = initial)
  unfold tunnelXmitSource
  simp (config := { zeta := false }) only [unsupported, skipCut]
  repeat' first
    | env_operation_fact loopback
    | env_operation_fact port
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_lift_from Net.M; exact liftRoute _)
    | (rx_retention_head liftRouting; exact routing _)
    | (rx_retention_head getRouting; exact routingRead)
    | (rx_retention_head getDev; exact dev)
    | (rx_retention_head get; exact read)
    | (rx_retention_head MonadStateOf.get; exact read)
    | (rx_retention_head modifyDev; exact edit _ (fun _ => rfl))
    | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
    | rx_retention_step

theorem send4ClearSrc_routing cache : SameView routingView (send4ClearSrcSource cache) := by
  intro initial
  unfold send4ClearSrcSource
  cases cache with
  | none => exact preserves_pure _
  | some pid =>
    apply hoare_bind _ _ (routing_getPeer (fun view => view = initial) pid)
    intro p
    exact routing_setPeer (fun view => view = initial) pid
      {p with endpoint := p.endpoint.map fun e => {e with src := 0, srcIf := 0}}

theorem send4Finish_routing e bytes ds exactRx route : SameView routingView (send4FinishSource e bytes ds exactRx route) := by
  intro initial
  let P := fun w : WGWorld => routingView w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (liftRouting a) :=
    hoare_liftRouting a P (fun _ _ hi => hi)
  have liftRoute {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) := routing a
  have routingRead : Preserves P (getRouting : WG.M Net.Routing) := routing ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  have dev : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp (fun v => v = initial)
  have edit (f : Device → Device) (hf : ∀ d, routingState (f d) = routingState d) :
      Preserves P (modifyDev f) := (modifyDev_routing f hf).wp (fun v => v = initial)
  have transmit := fun r => show Preserves P _ from
    (tunnelXmit_routing e bytes ds r exactRx).wp (fun v => v = initial)
  unfold send4FinishSource
  simp (config := { zeta := false }) only [invariant, ]
  repeat' first
    | env_operation_fact transmit
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_lift_from Net.M; exact liftRoute _)
    | (rx_retention_head liftRouting; exact routing _)
    | (rx_retention_head getRouting; exact routingRead)
    | (rx_retention_head getDev; exact dev)
    | (rx_retention_head get; exact read)
    | (rx_retention_head MonadStateOf.get; exact read)
    | (rx_retention_head modifyDev; exact edit _ (fun _ => rfl))
    | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
    | rx_retention_step

theorem send4RouteDone_routing e cache bytes ds exactRx gen fallback rt :
    SameView routingView (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  intro initial
  let P := fun w : WGWorld => routingView w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (liftRouting a) :=
    hoare_liftRouting a P (fun _ _ hi => hi)
  have liftRoute {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) := routing a
  have routingRead : Preserves P (getRouting : WG.M Net.Routing) := routing ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  have dev : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp (fun v => v = initial)
  have edit (f : Device → Device) (hf : ∀ d, routingState (f d) = routingState d) :
      Preserves P (modifyDev f) := (modifyDev_routing f hf).wp (fun v => v = initial)
  have cacheSet := fun pid src gen dev => show Preserves P _ from
    (dstCacheSet_routing pid src gen dev).wp (fun v => v = initial)
  have done := fun r => show Preserves P _ from
    (send4Finish_routing e bytes ds exactRx r).wp (fun v => v = initial)
  unfold send4RouteDoneSource
  simp (config := { zeta := false }) only [branch, ]
  repeat' first
    | env_operation_fact cacheSet
    | env_operation_fact done
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_lift_from Net.M; exact liftRoute _)
    | (rx_retention_head liftRouting; exact routing _)
    | (rx_retention_head getRouting; exact routingRead)
    | (rx_retention_head getDev; exact dev)
    | (rx_retention_head get; exact read)
    | (rx_retention_head MonadStateOf.get; exact read)
    | (rx_retention_head modifyDev; exact edit _ (fun _ => rfl))
    | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
    | rx_retention_step

theorem send4Retry_routing e cache bytes ds exactRx gen fallback srcIf rt :
    SameView routingView (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  intro initial
  let P := fun w : WGWorld => routingView w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (liftRouting a) :=
    hoare_liftRouting a P (fun _ _ hi => hi)
  have liftRoute {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) := routing a
  have routingRead : Preserves P (getRouting : WG.M Net.Routing) := routing ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  have dev : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp (fun v => v = initial)
  have edit (f : Device → Device) (hf : ∀ d, routingState (f d) = routingState d) :
      Preserves P (modifyDev f) := (modifyDev_routing f hf).wp (fun v => v = initial)
  have clear : Preserves P (send4ClearSrcSource cache) :=
    (send4ClearSrc_routing cache).wp (fun v => v = initial)
  have reset := fun pid => show Preserves P _ from
    (dstCacheReset_routing pid).wp (fun v => v = initial)
  have done := fun rt => show Preserves P _ from
    (send4RouteDone_routing e cache bytes ds exactRx gen fallback rt).wp (fun v => v = initial)
  unfold send4RetrySource
  simp (config := { zeta := false }) only [branch, ]
  repeat' first
    | env_operation_fact clear
    | env_operation_fact reset
    | env_operation_fact done
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_lift_from Net.M; exact liftRoute _)
    | (rx_retention_head liftRouting; exact routing _)
    | (rx_retention_head getRouting; exact routingRead)
    | (rx_retention_head getDev; exact dev)
    | (rx_retention_head get; exact read)
    | (rx_retention_head MonadStateOf.get; exact read)
    | (rx_retention_head modifyDev; exact edit _ (fun _ => rfl))
    | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
    | rx_retention_step

theorem send4Miss_routing e cache bytes ds exactRx gen fallback saddr srcIf :
    SameView routingView (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  intro initial
  let P := fun w : WGWorld => routingView w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (liftRouting a) :=
    hoare_liftRouting a P (fun _ _ hi => hi)
  have liftRoute {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) := routing a
  have routingRead : Preserves P (getRouting : WG.M Net.Routing) := routing ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  have dev : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp (fun v => v = initial)
  have edit (f : Device → Device) (hf : ∀ d, routingState (f d) = routingState d) :
      Preserves P (modifyDev f) := (modifyDev_routing f hf).wp (fun v => v = initial)
  have clear : Preserves P (send4ClearSrcSource cache) :=
    (send4ClearSrc_routing cache).wp (fun v => v = initial)
  have reset := fun pid => show Preserves P _ from
    (dstCacheReset_routing pid).wp (fun v => v = initial)
  have retry := fun srcIf rt => show Preserves P _ from
    (send4Retry_routing e cache bytes ds exactRx gen fallback srcIf rt).wp (fun v => v = initial)
  unfold send4MissSource
  simp (config := { zeta := false }) only [branch, ]
  repeat' first
    | env_operation_fact clear
    | env_operation_fact reset
    | env_operation_fact retry
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_lift_from Net.M; exact liftRoute _)
    | (rx_retention_head liftRouting; exact routing _)
    | (rx_retention_head getRouting; exact routingRead)
    | (rx_retention_head getDev; exact dev)
    | (rx_retention_head get; exact read)
    | (rx_retention_head MonadStateOf.get; exact read)
    | (rx_retention_head modifyDev; exact edit _ (fun _ => rfl))
    | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
    | rx_retention_step

theorem send4AfterCache_routing e cache bytes ds exactRx gen saddr srcIf route :
    SameView routingView (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  intro initial
  let P := fun w : WGWorld => routingView w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (liftRouting a) :=
    hoare_liftRouting a P (fun _ _ hi => hi)
  have liftRoute {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) := routing a
  have routingRead : Preserves P (getRouting : WG.M Net.Routing) := routing ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  have dev : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp (fun v => v = initial)
  have edit (f : Device → Device) (hf : ∀ d, routingState (f d) = routingState d) :
      Preserves P (modifyDev f) := (modifyDev_routing f hf).wp (fun v => v = initial)
  have miss : Preserves P (send4MissSource e cache bytes ds exactRx gen route saddr srcIf) :=
    (send4Miss_routing e cache bytes ds exactRx gen route saddr srcIf).wp (fun v => v = initial)
  have done : Preserves P (send4FinishSource e bytes ds exactRx route) :=
    (send4Finish_routing e bytes ds exactRx route).wp (fun v => v = initial)
  unfold send4AfterCacheSource
  simp (config := { zeta := false }) only [branch, ]
  repeat' first
    | env_operation_fact miss
    | env_operation_fact done
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_lift_from Net.M; exact liftRoute _)
    | (rx_retention_head liftRouting; exact routing _)
    | (rx_retention_head getRouting; exact routingRead)
    | (rx_retention_head getDev; exact dev)
    | (rx_retention_head get; exact read)
    | (rx_retention_head MonadStateOf.get; exact read)
    | (rx_retention_head modifyDev; exact edit _ (fun _ => rfl))
    | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
    | rx_retention_step

theorem send4_routing e cache bytes ds exactRx : SameView routingView (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  intro initial
  let P := fun w : WGWorld => routingView w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (liftRouting a) :=
    hoare_liftRouting a P (fun _ _ hi => hi)
  have liftRoute {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) := routing a
  have routingRead : Preserves P (getRouting : WG.M Net.Routing) := routing ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  have dev : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp (fun v => v = initial)
  have edit (f : Device → Device) (hf : ∀ d, routingState (f d) = routingState d) :
      Preserves P (modifyDev f) := (modifyDev_routing f hf).wp (fun v => v = initial)
  have cached := fun pid gen => show Preserves P _ from
    (dstCacheGet_routing pid gen).wp (fun v => v = initial)
  have after := fun gen src srcIf route => show Preserves P _ from
    (send4AfterCache_routing e cache bytes ds exactRx gen src srcIf route).wp (fun v => v = initial)
  unfold send4Source
  simp (config := { zeta := false }) only [branch, invariant, ]
  repeat' first
    | env_operation_fact cached
    | env_operation_fact after
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_lift_from Net.M; exact liftRoute _)
    | (rx_retention_head liftRouting; exact routing _)
    | (rx_retention_head getRouting; exact routingRead)
    | (rx_retention_head getDev; exact dev)
    | (rx_retention_head get; exact read)
    | (rx_retention_head MonadStateOf.get; exact read)
    | (rx_retention_head modifyDev; exact edit _ (fun _ => rfl))
    | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
    | rx_retention_step

theorem send6_routing e cache bytes ds exactRx : SameView routingView (send6 e cache bytes ds exactRx) := by
  intro initial
  let P := fun w : WGWorld => routingView w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have routing {α : Type} (a : Net.M α) : Preserves P (liftRouting a) :=
    hoare_liftRouting a P (fun _ _ hi => hi)
  have liftRoute {α : Type} (a : Net.M α) : Preserves P (monadLift a : WG.M α) := routing a
  have routingRead : Preserves P (getRouting : WG.M Net.Routing) := routing ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  have dev : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp (fun v => v = initial)
  have edit (f : Device → Device) (hf : ∀ d, routingState (f d) = routingState d) :
      Preserves P (modifyDev f) := (modifyDev_routing f hf).wp (fun v => v = initial)
  have readBind {α : Type} (pid : PeerId) (f : Peer → WG.M α)
      (hf : ∀ p, initial.bind (fun view => view.lists pid) = some p.allowedipsList →
        Preserves P (f p)) : Preserves P (getPeer pid >>= f) := by
    apply hoare_bind _ _ (routing_getPeer (fun view => view = initial) pid)
    intro p
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' h hr
    have saved : (routingView w).bind (fun view => view.lists pid) = some p.allowedipsList := by
      simpa only [routingView, routingState, Option.bind_map, Function.comp_def] using h.2
    rw [h.1] at saved
    exact (hoare_iff_run_ambient _ _ _).mp (hf p saved) w ambient x v ambient' h.1 hr
  have knownSet (pid : PeerId) (p : Peer)
      (hp : initial.bind (fun view => view.lists pid) = some p.allowedipsList) :
      Preserves P (setPeer pid p) := by
    apply hoare_consequence (routing_setPeer (fun view => view = initial) pid p)
    · intro w h
      refine ⟨h, ?_⟩
      have current : (routingView w).bind (fun view => view.lists pid) = some p.allowedipsList := by
        rw [h]; exact hp
      simpa only [routingView, routingState, Option.bind_map, Function.comp_def] using current
    · exact fun _ _ h => h
  have cached := fun pid gen => show Preserves P _ from
    (dstCacheGet_routing pid gen).wp (fun v => v = initial)
  have reset := fun pid => show Preserves P _ from
    (dstCacheReset_routing pid).wp (fun v => v = initial)
  have cacheSet := fun pid src gen dev => show Preserves P _ from
    (dstCacheSet_routing pid src gen dev).wp (fun v => v = initial)
  have transmit := fun r => show Preserves P _ from
    (tunnelXmit_routing e bytes ds r exactRx).wp (fun v => v = initial)
  unfold send6
  simp (config := { zeta := false }) only [branch, invariant, ]
  repeat' first
    | (run_tac Lean.Elab.Tactic.withMainContext do
        let target := (← Lean.Elab.Tactic.getMainTarget).consumeMData
        unless target.isAppOf ``Preserves && target.getAppArgs.size > 0 do
          throwError "not a routing preservation contract"
        let action := target.getAppArgs.back!.consumeMData.headBeta
        unless action.isAppOf ``Bind.bind && action.getAppArgs.size ≥ 2 do
          throwError "not a bind"
        let first := action.getAppArgs[action.getAppArgs.size - 2]!.consumeMData
        unless first.isAppOf ``getPeer do throwError "not a peer read"
       apply readBind
       intro p hp)
    | (rx_retention_head setPeer; apply knownSet; exact hp)
    | env_operation_fact cached
    | env_operation_fact reset
    | env_operation_fact cacheSet
    | env_operation_fact transmit
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_lift_from Net.M; exact liftRoute _)
    | (rx_retention_head liftRouting; exact routing _)
    | (rx_retention_head getRouting; exact routingRead)
    | (rx_retention_head getDev; exact dev)
    | (rx_retention_head get; exact read)
    | (rx_retention_head MonadStateOf.get; exact read)
    | (rx_retention_head modifyDev; exact edit _ (fun _ => rfl))
    | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
    | rx_retention_step

end Leanux.Proofs.WG.AllowedIps
