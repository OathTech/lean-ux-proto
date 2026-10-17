import Leanux.Proofs.WG.Origins.HistorySupport
import Leanux.Proofs.WG.Queues.RxScheduleHistory

/-! Stateful origin support through the existing receive/crypt/scheduler spine.
The source observers and their input histories are unchanged. Copied trial
executions are not injected into the committed journal. -/
namespace Leanux.Proofs.WG.Origins.HistorySupport
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Retaining Std.Do

private theorem endpoint_material (pid : PeerId) (src : SkbSource) :
    SameView view (setPeerEndpointFromSkb pid src) := by
  intro initial
  unfold setPeerEndpointFromSkb endpointFromSkb
  material_lower
  repeat' first
    | (index_material_head setPeerEndpoint; exact (setPeerEndpoint_material _ _).wp (fun t => t = initial))
    | material_basic (fun t => t = initial)

private theorem reply_material (src : SkbSource) (bytes : List UInt8) :
    SameView view (sendBufferAsReplyToSkb src bytes) := by
  intro initial
  unfold sendBufferAsReplyToSkb endpointFromSkb
  material_lower
  repeat' first
    | (index_material_head send4; exact (send4_material _ _ _ _ _).wp (fun t => t = initial))
    | (index_material_head send6; exact (send6_material _ _ _ _ _).wp (fun t => t = initial))
    | material_basic (fun t => t = initial)

private theorem cookieSend_material (msg : List UInt8) (src : SkbSource) :
    SameView view (sendHandshakeCookie msg src) := by
  intro initial
  unfold sendHandshakeCookie
  repeat' first
    | (index_material_head cookieMessageCreate
       exact (cookie_material_native _
         ((cookieMessageCreate_sameCookie _ _ _).factor WGOwnedView.toWGStoreView)).wp (fun t => t = initial))
    | (index_material_head sendBufferAsReplyToSkb; exact (reply_material _ _).wp (fun t => t = initial))
    | material_basic (fun t => t = initial)

private theorem publish_material (id : SkbId) (state : PacketState) :
    SameView view (RxWorkers.publishSource id state) := by
  intro initial
  unfold RxWorkers.publishSource
  material_lower
  repeat' first
    | material_basic (fun t => t = initial)
    | traffic_basic (fun t => t = initial)

def Focused (enc : E → Event) (dec : Event → Option E) (a : PrefixM E α) : Prop :=
  Appends a ∧ Preserves (focusPrefix enc dec a)

theorem focused_bind (enc : E → Event) (dec : Event → Option E)
    (hd : ∀ e, dec (enc e) = some e) (a : PrefixM E α) (b : α → PrefixM E β)
    (ha : Focused enc dec a) (hb : ∀ x, Focused enc dec (b x)) :
    Focused enc dec (a >>= b) :=
  ⟨Appends.bind ha.1 (fun x => (hb x).1),
    focus_bind enc dec hd a b ha.1 (fun x => (hb x).1) ha.2 (fun x => (hb x).2)⟩

theorem focused_pure (enc : E → Event) (dec : Event → Option E) (x : α) :
    Focused enc dec (pure x) := ⟨Appends.pure x, focus_pure enc dec x⟩

theorem focused_lift (enc : E → Event) (dec : Event → Option E) (a : Leanux.M α)
    (ha : ProductRetainsCall a) : Focused enc dec (liftPrefix a) :=
  ⟨Appends.lift a, focus_lift enc dec a ha⟩

theorem focused_ite (enc : E → Event) (dec : Event → Option E) (p : Prop) [Decidable p]
    (ha : p → Focused enc dec a) (hb : ¬p → Focused enc dec b) :
    Focused enc dec (if p then a else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact ha hp
  · exact hb hp

-- Dispatch on unreduced source heads, avoiding speculative unfolding of whole
-- continuations or of the stateful semantic predicate.
elab "support_intro" : tactic => do
  unless (← Lean.Elab.Tactic.getMainTarget).isForall do
    Lean.throwError "expected continuation"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro x; try dsimp only))

elab "support_at " wanted:str : tactic => do
  let t ← Lean.Elab.Tactic.getMainTarget
  unless t.isAppOf ``Focused do Lean.throwError "expected support contract"
  let mut a := t.getAppArgs.back!
  if a.isAppOf ``HistoryAdapters.focus || a.isAppOf ``focusPrefix then
    a := a.getAppArgs.back!
  if a.isAppOf ``HistoryAdapters.life || a.isAppOf ``MaterialOrigin.access then
    a := a.getAppArgs.back!
  if a.isAppOf ``liftWGObserver then a := a.getAppArgs.back!
  if (a.getAppFn.constName?.map Lean.Name.toString |>.getD "").endsWith ".accessState" then
    a := a.getAppArgs.back!
  a := a.headBeta
  let name := a.getAppFn.constName?.map Lean.Name.toString |>.getD ""
  unless name.endsWith wanted.getString do
    Lean.throwError "different source head: {name}"

elab "support_append_goal" : tactic => do
  unless (← Lean.Elab.Tactic.getMainTarget).isAppOf ``Appends do
    Lean.throwError "expected append contract"

-- The Ambient-only invariant/unsupported wrappers are subsumed at their
-- actual product use sites by the canonical Ambient lift rule.
macro "support_material" : tactic => `(tactic| (
  intro initial
  refine hoare_consequence (m := Except Stop)
    (P := fun w : World => RetainsView initial (view w.wg))
    (Q := fun _ (w : World) => RetainsView initial (view w.wg)) ?_
    (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _)
    (fun _ _ h => h)
  try material_lower
  try simp (config := {zeta := false}) only [peekHiddenSite,recordBudget,budgetExhausted,peekUnit,resolveUnit]
  repeat' first
    | (index_material_head Env.condResched
       exact (kernel (project := id) (condResched_sameKernel _)).wp (RetainsView initial))
    | (index_material_head Cookies.loadPhase
       exact (sameView_of_sameWG (project := id) Cookies.loadPhase_sameStore).wp (RetainsView initial))
    | (index_material_head cookieValidatePacket
       exact (cookie_material_native _
         ((cookieValidatePacket_sameCookie _ _ _).factor WGOwnedView.toWGStoreView)).wp (RetainsView initial))
    | material_basic (RetainsView initial)
    | traffic_product_basic initial))

macro "support_native_material" : tactic => `(tactic| (
  intro initial
  refine hoare_consequence (m := AmbientM)
    (P := fun w : WGWorld => RetainsView initial (view w))
    (Q := fun _ (w : WGWorld) => RetainsView initial (view w)) ?_
    (fun w h => by change view w = initial at h; rw [h]; exact RetainsView.refl _)
    (fun _ _ h => h)
  try material_lower
  repeat' first
    | material_basic (RetainsView initial)
    | traffic_basic (RetainsView initial)))

private theorem native_mixed (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (he : ErasesStatePrefix g a) (ha : RetainsCall a) :
    Preserves (RxHistory.mixed (liftWGObserver g)) :=
  mixed _ _ (liftWGObserver_erases he) (RetainsCall.product ha)

macro "support_focused" : tactic => `(tactic| first
  | (support_at "Origins.localSession"; exact ⟨(StateAppends.focus _ _ _).liftWGObserver, session _⟩)
  | (support_at "modifyPeerKeysPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases (modifyPeerKeysPrefix_erases _ _)) (RetainsCall.product (of_view (modifyPeer_material _ _)))⟩)
  | (support_at "createResponsePrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases (createResponsePrefix_erases _)) (RetainsCall.product (of_view (createResponse_material _)))⟩)
  | (support_at "addMacToPacketPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases (addMacToPacketPrefix_erases _ _)) (RetainsCall.product (of_view (addMacToPacket_material _ _)))⟩)
  | (support_at "sendBufferToPeerPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases (sendBufferToPeerPrefix_erases _ _)) (RetainsCall.product (of_view (sendBufferToPeer_material _ _)))⟩)
  | (support_at "timersSessionDerivedPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases (timersSessionDerivedPrefix_erases _)) (RetainsCall.product (of_view (timersSessionDerived_material _)))⟩)
  | (support_at "timersTraversalPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases (timersTraversalPrefix_erases _)) (RetainsCall.product (of_view (timersTraversal_material _)))⟩)
  | (support_at "timersAnyAuthenticatedPacketSentPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases (timersAnyAuthenticatedPacketSentPrefix_erases _)) (RetainsCall.product (of_view (timersAnyAuthenticatedPacketSent_material _)))⟩)
  | (support_at "sendHandshakeCookiePrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases (sendHandshakeCookiePrefix_erases _ _)) (RetainsCall.product (of_view (cookieSend_material _ _)))⟩)
  | (support_at "consumeInitiationPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases (consumeInitiationPrefix_erases _)) (RetainsCall.product (consumeInitiation_material _))⟩)
  | (support_at "consumeResponsePrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases (consumeResponsePrefix_erases _)) (RetainsCall.product (consumeResponse_material _))⟩)
  | (support_at "setPeerEndpointFromSkbPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases (setPeerEndpointFromSkbPrefix_erases _ _)) (RetainsCall.product (of_view (endpoint_material _ _)))⟩)
  | (support_at "timersHandshakeCompletePrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases (timersHandshakeCompletePrefix_erases _ _)) (RetainsCall.product (of_view (timersHandshakeComplete_material _ _)))⟩)
  | (support_at "sendKeepalivePrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases (sendKeepalivePrefix_erases _)) (RetainsCall.product (sendKeepalive_material _))⟩)
  | (support_at "timersAnyAuthenticatedPacketReceivedPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases (timersAnyAuthenticatedPacketReceivedPrefix_erases _)) (RetainsCall.product (of_view (timersAnyAuthenticatedPacketReceived_material _)))⟩)
  | (support_at "peerPutMixed"; exact ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases (peerPutMixed_erases _)) (RetainsCall.product (of_view (peerPut_material _)))⟩)
  | (support_at "cookieMessageConsumePrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (liftWGObserver_erases (cookieMessageConsumePrefix_erases _)) (RetainsCall.product (cookieMessageConsume_material _))⟩)
  | (support_at "liftPrefix"; apply focused_lift; support_material)
  | (support_at "Pure.pure"; exact focused_pure _ _ _)
  | (support_at "Bind.bind"; apply focused_bind _ _ HistoryAdapters.decode_encode)
  | (support_at "ite"; apply focused_ite)
  | (support_append_goal; support_appends)
  | support_intro
  | split)

private theorem response_focused (pid : PeerId) :
    Focused HistoryAdapters.encode HistoryAdapters.decode (HistoryAdapters.localResponse pid) := by
  unfold HistoryAdapters.localResponse HandshakeSources.responseWith
  dsimp only [HistoryAdapters.ops]
  repeat' support_focused

theorem response (pid : PeerId) : Preserves (HistoryAdapters.focus (HistoryAdapters.localResponse pid)) :=
  (response_focused pid).2

private theorem afterMac_focused (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    Focused HistoryAdapters.encode HistoryAdapters.decode (HistoryAdapters.localAfterMac msg src loaded mac) := by
  unfold HistoryAdapters.localAfterMac HandshakeSources.afterMacWith
  simp only [← HistoryAdapters.localResponse_eq]
  dsimp only [HistoryAdapters.ops]
  repeat' first | (support_at "localResponse"; exact response_focused _) | support_focused

theorem afterMac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    Preserves (HistoryAdapters.focus (HistoryAdapters.localAfterMac msg src loaded mac)) :=
  (afterMac_focused msg src loaded mac).2

private theorem reception_focused (msg : List UInt8) (src : SkbSource) :
    Focused HistoryAdapters.encode HistoryAdapters.decode (HistoryAdapters.localReception msg src) := by
  unfold HistoryAdapters.localReception HandshakeSources.receptionWith
  simp only [← HistoryAdapters.localAfterMac_eq]
  dsimp only [HistoryAdapters.ops]
  repeat' first | (support_at "localAfterMac"; exact afterMac_focused _ _ _ _) | support_focused

theorem reception (msg : List UInt8) (src : SkbSource) :
    Preserves (HistoryAdapters.focus (HistoryAdapters.localReception msg src)) :=
  (reception_focused msg src).2

theorem receiveStep : Preserves HistoryAdapters.receiveStep := by
  have h : Focused HistoryAdapters.encode HistoryAdapters.decode HistoryAdapters.localStep := by
    unfold HistoryAdapters.localStep HandshakeSources.stepWith
    simp only [← HistoryAdapters.localReception_eq]
    dsimp only [HistoryAdapters.ops]
    repeat' first | (support_at "localReception"; exact reception_focused _ _) | support_focused
  exact h.2

theorem prepare : Preserves HistoryAdapters.prepare := by
  have hp : Focused rxEncode rxDecode (liftWGObserver RxOrigin.prepare) := by
    unfold RxOrigin.prepare RxOrigin.prepareWith
    simp only [monadLift_self]
    repeat' first
      | (rw [liftWGObserver_lift])
      | (rw [liftWGObserver_bind])
      | (rw [liftWGObserver_pure])
      | (support_at "RxOrigin.decrypt"; exact ⟨((StateAppends.focus _ _ _).receiptWGObserved _).liftWGObserver, rx_decrypt _⟩)
      | (support_at "setRxSkbPrefix"; exact ⟨(StateAppends.focus _ _ _).liftWGObserver, rx_life _ _ (liftWGObserver_erases (setRxSkbPrefix_erases _ _)) (by support_material)⟩)
      | (support_at "RxWorkers.publishPrefix"; exact ⟨(StateAppends.focus _ _ _).liftWGObserver, rx_life _ _ (liftWGObserver_erases (RxWorkers.publish_erases _ _)) (RetainsCall.product (of_view (publish_material _ _)))⟩)
      | (support_at "liftPrefix"; apply focused_lift; support_material)
      | (support_at "Pure.pure"; exact focused_pure _ _ _)
      | (support_at "Bind.bind"; apply focused_bind _ _ rx_decode_encode)
      | (support_at "ite"; apply focused_ite)
      | support_intro
      | split
  apply congr hp.2
  intro w h
  exact (focus_compose _ _ _ _ _ w h).symm


theorem receiveIteration : Preserves HistoryAdapters.receiveIteration :=
  workerIterPrefix_preserves _ _ safe receiveStep (lift_kernel _ (condResched_sameKernel _))

private theorem pending_material : RetainsCall RxNapi.pendingSource := by
  apply of_view
  intro initial
  unfold RxNapi.pendingSource
  repeat' material_basic (fun t => t = initial)

private theorem scheduled_material : RetainsCall RxNapi.scheduledSource := by
  apply of_view
  intro initial
  unfold RxNapi.scheduledSource
  repeat' material_basic (fun t => t = initial)

theorem napiSoftirq : Preserves RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves safe (fun _ _ _ he hi => hi.kernel he)
    (native_mixed _ _ RxNapi.pending_erases pending_material) poll

theorem pollScheduledInline : Preserves RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves safe (fun _ _ _ he hi => hi.kernel he)
    (native_mixed _ _ RxNapi.pending_erases pending_material) poll

theorem napiIrqExit : Preserves RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves safe (fun _ _ _ he hi => hi.kernel he)
    (native_mixed _ _ RxNapi.scheduled_erases scheduled_material) napiSoftirq

private theorem encryptTail_material (item : Option (List SkbId)) :
    ProductRetainsCall (RxWorkers.encryptTailSource item) := by
  unfold RxWorkers.encryptTailSource
  apply workerIter_material
  · intro initial
    refine hoare_consequence (m := Except Stop)
      (P := fun w : World => RetainsView initial (view w.wg))
      (Q := fun _ (w : World) => RetainsView initial (view w.wg)) ?_
      (fun w h => by change view w.wg = initial at h; rw [h]; exact RetainsView.refl _)
      (fun _ _ h => h)
    unfold RxWorkers.encryptStepTailSource
    material_lower
    repeat' first
      | (index_material_head encryptPacket
         exact ProjectedRetainsCall.wp (encryptPacket_material _ actualChecksum_material _ _) initial)
      | (index_material_head enqueuePerPeerTx; exact (enqueuePerPeerTx_material _ _).wp initial)
      | traffic_product_basic initial
  · support_material

private theorem pendingNapi_material (next : Option Nat) : ProductRetainsCall (pendingNapi next) := by
  unfold pendingNapi
  support_material

theorem source_get : SameProductStore (get : Leanux.M World) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x v hr
  cases hr
  rfl

theorem source_modify (f : World → World)
    (hf : ∀ w, productStoreView (f w) = productStoreView w) :
    SameProductStore (modify f) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x v hr
  cases hr
  exact hf w

theorem source_throw (α : Type) (e : Stop) : SameProductStore (throw e : Leanux.M α) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x v hr
  cases hr

theorem mixed_lift (a : Leanux.M α) (ha : ProductRetainsCall a) :
    Preserves (RxHistory.mixed (liftPrefix a)) :=
  mixed _ _ (erasesPrefix_lift a) ha

theorem mixed_throw (α : Type) (e : Stop) :
    Preserves (RxHistory.mixed (throw e : PrefixM LifetimeEvent α)) :=
  mixed _ _ (erasesPrefix_throw e) (of_view (kernel (source_throw α e)))

macro "support_kernel" : tactic => `(tactic| first
  | exact source_get
  | exact source_modify _ (fun _ => rfl)
  | exact source_throw _ _
  | exact liftWG_sameProductStore _ getDev_sameWGStore
  | exact condResched_sameKernel _
  | exact activationOccupancy_sameKernel _
  | exact activationHasWork_sameKernel _
  | (intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi)))

open Lean Meta Elab Tactic in
elab "support_step_at " wanted:str : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Preserves || target.isAppOf ``PrefixPreserves do
    throwError "not a history-support contract"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let mut action := args.back!.consumeMData
  if action.isAppOf ``RxHistory.mixed then action := action.getAppArgs.back!
  if action.isAppOf ``liftWGObserver then action := action.getAppArgs.back!
  action := action.headBeta
  let name := action.getAppFn.constName?.map Name.toString |>.getD ""
  unless name.endsWith wanted.getString do throwError "different observer head: {name}"

open Lean Meta Elab Tactic in
elab "support_action_match" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Focused || target.isAppOf ``Preserves ||
      target.isAppOf ``PrefixPreserves do throwError "not a history-support contract"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let mut action := args.back!.consumeMData
  if action.isAppOf ``liftWGObserver then action := action.getAppArgs.back!
  let some _ ← matchMatcherApp? action | throwError "not an observer matcher"
  replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)

macro "support_steps" : tactic => `(tactic|
  first
    | (support_step_at "HistoryAdapters.prepare"; exact prepare)
    | (support_step_at "HistoryAdapters.receiveIteration"; exact receiveIteration)
    | (support_step_at "peerPutMixed"; exact native_mixed _ _ (peerPutMixed_erases _) (of_view (peerPut_material _)))
    | (support_step_at "getPeerMixed"; exact native_mixed _ _ (getPeerMixed_erases _) (of_view (getPeer_material _)))
    | (support_step_at "getTxSkbPrefix"; exact native_mixed _ _ (getTxSkbPrefix_erases _) (by support_native_material))
    | (support_step_at "activationOccupancyPrefix"; exact mixed _ _ (activationOccupancyPrefix_erases _) (of_view (kernel (activationOccupancy_sameKernel _))))
    | (support_step_at "activationHasWorkPrefix"; exact mixed _ _ (activationHasWorkPrefix_erases _) (of_view (kernel (activationHasWork_sameKernel _))))
    | (support_step_at "pendingNapiPrefix"; exact mixed _ _ (pendingNapiPrefix_erases _) (pendingNapi_material _))
    | (support_step_at "txIterPrefix"; exact mixed _ _ (txIterPrefix_erases _ (erasesPrefix_lift _)) (actualTxIter_material _))
    | (support_step_at "liftWGPrefix"; exact native_mixed _ _ (erasesStatePrefix_lift _) (by support_native_material))
    | (support_step_at "liftPrefix"; first
        | exact mixed_lift _ (by support_material)
        | exact lift_retains _ (by support_material))
    | (support_step_at "throw"; exact mixed_throw _ _)
    | (support_step_at "Pure.pure"; exact PrefixPreserves.pure safe _)
    | (support_step_at "ForIn.forIn"; first
        | apply PrefixPreserves.range (State := World) _ _ _ safe
        | apply PrefixPreserves.forIn _ _ _ safe)
    | (support_step_at "Bind.bind"; apply PrefixPreserves.bind)
    | (support_step_at "ite"; split)
    | support_action_match
    | support_intro)

theorem encryptIteration : Preserves RxHistory.encryptIteration := by
  apply PrefixPreserves.bind
  · apply native_mixed _ _ (erasesStatePrefix_lift _)
    apply of_view
    intro initial
    unfold TxRing.pollSource
    repeat' material_basic (fun t => t = initial)
  · intro item
    exact PrefixPreserves.bind napiSoftirq (fun _ =>
      mixed _ _ (RxWorkers.encryptTail_erases item) (encryptTail_material item))

theorem decryptStep : Preserves RxHistory.decryptStep := by
  unfold RxHistory.decryptStep RxWorkers.decryptWith
  repeat' first
    | (support_step_at "RxHistory.napiSoftirq"; exact napiSoftirq)
    | (support_step_at "RxHistory.napiIrqExit"; exact napiIrqExit)
    | support_steps

theorem decryptIteration : Preserves RxHistory.decryptIteration := by
  apply workerIterPrefix_preserves _ _ safe decryptStep
  exact PrefixPreserves.bind (lift_kernel _ (condResched_sameKernel _))
    (fun _ => lift_kernel _ (by intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi)))

theorem cryptAhead (pid : PeerId) : Preserves (RxHistory.cryptAhead pid) := by
  unfold RxHistory.cryptAhead
  repeat' first | (support_step_at "RxHistory.encryptIteration"; exact encryptIteration) | support_steps

theorem activationIteration (a : Activation) : Preserves (RxHistory.activationIteration a) := by
  unfold RxHistory.activationIteration
  repeat' first
    | (support_step_at "RxHistory.encryptIteration"; exact encryptIteration)
    | (support_step_at "RxHistory.decryptIteration"; exact decryptIteration)
    | (support_step_at "RxHistory.cryptAhead"; exact cryptAhead _)
    | support_steps

theorem activationRun (a : Activation) : Preserves (RxHistory.activationRun a) := by
  unfold RxHistory.activationRun
  repeat' first | (support_step_at "RxHistory.activationIteration"; exact activationIteration _) | support_steps

theorem dispatch (worker : Worker) : Preserves (RxHistory.dispatch worker) := by
  unfold RxHistory.dispatch
  repeat' first | (support_step_at "RxHistory.activationRun"; exact activationRun _) | support_steps

/-- The actual saved probe is checked before the copied-world filter executes.
No receipt from a copied trial is claimed to occur in this committed journal. -/
theorem schedule (stack : Option Worker) : Preserves (RxHistory.schedule stack) := by
  unfold RxHistory.schedule
  simp only [List.find?_cons,List.find?_nil]
  repeat' first
    | (support_step_at "RxHistory.dispatch"; exact dispatch _)
    | (support_step_at "RxHistory.activationRun"; exact activationRun _)
    | (support_step_at "RxHistory.napiSoftirq"; exact napiSoftirq)
    | (support_step_at "RxHistory.audit"; exact filter_probe)
    | support_steps

theorem nestedResched (self : Worker) : Preserves (RxHistory.nestedResched self) := by
  unfold RxHistory.nestedResched
  apply PrefixPreserves.bind (lift_kernel _ (condResched_sameKernel _))
  intro b
  split
  · exact schedule _
  · exact PrefixPreserves.pure safe _

end Leanux.Proofs.WG.Origins.HistorySupport
