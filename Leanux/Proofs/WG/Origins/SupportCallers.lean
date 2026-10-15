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
  apply SameView.of_wp
  intro s
  have he := (kernel (endpointFromSkb_sameKernel src)).wp (fun t => t = s)
  have hs := fun e => (setPeerEndpoint_material pid e).wp (fun t => t = s)
  mvcgen [setPeerEndpointFromSkb,he,hs,branch,invariant]

private theorem reply_material (src : SkbSource) (bytes : List UInt8) :
    SameView view (sendBufferAsReplyToSkb src bytes) := by
  apply SameView.of_wp
  intro s
  have ha := (kernel (hiddenAlloc_sameKernel .replySkb)).wp (fun t => t = s)
  have he := (kernel (endpointFromSkb_sameKernel src)).wp (fun t => t = s)
  have h4 := fun e => (send4_material e none bytes 0 false).wp (fun t => t = s)
  have h6 := fun e => (send6_material e none bytes 0 false).wp (fun t => t = s)
  have hd (α : Type) := discard_view_spec view (α := α) (fun t => t = s)
  mvcgen [sendBufferAsReplyToSkb,ha,he,h4,h6,hd,branch,invariant]

private theorem cookieSend_material (msg : List UInt8) (src : SkbSource) :
    SameView view (sendHandshakeCookie msg src) := by
  apply SameView.of_wp
  intro s
  have hc := fun i mac => (cookie_material _ (cookieMessageCreate_sameCookieKernel i src mac)).wp (fun t => t = s)
  have hs := fun bytes => (reply_material src bytes).wp (fun t => t = s)
  mvcgen [sendHandshakeCookie,hc,hs]

private theorem publish_material (id : SkbId) (state : PacketState) :
    SameView view (RxWorkers.publishSource id state) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hg := (getRxSkb_material id).wp P
  have hw := fun o => (ownerDeref_material o).wp P
  have hr := fun pid => (peerGet_material pid).wp P
  have hp := fun pid => (getPeer_material pid).wp P
  have hs := fun pid p => (setPeer_view pid p).wp P
  have hx := fun f => (setRxSkb_material id f).wp P
  mvcgen [RxWorkers.publishSource,hg,hw,hr,hp,hs,hx,invariant]

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

theorem focused_lift (enc : E → Event) (dec : Event → Option E) (a : M α)
    (ha : RetainsCall a) : Focused enc dec (liftPrefix a) :=
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
  a := a.headBeta
  let name := a.getAppFn.constName?.map Lean.Name.toString |>.getD ""
  unless name.endsWith wanted.getString do
    Lean.throwError "different source head: {name}"

elab "support_append_goal" : tactic => do
  unless (← Lean.Elab.Tactic.getMainTarget).isAppOf ``Appends do
    Lean.throwError "expected append contract"

theorem invariant_material (α : Type) (msg : String) : RetainsCall (invariant msg : M α) :=
  of_view (kernel (by intro w x v hr; simp [invariant] at hr))

theorem unsupported_material (α : Type) (msg : String) : RetainsCall (unsupported msg : M α) :=
  of_view (kernel (by intro w x v hr; simp [unsupported] at hr))

macro "support_material" : tactic => `(tactic| first
  | with_reducible exact invariant_material _ _
  | exact of_view (kernel getDev_sameKernel)
  | exact of_view (kernel getK_sameKernel)
  | with_reducible exact of_view (kernel (orM_sameKernel (andM_sameKernel (sameKernel_branch _ _) (sameKernel_branch _ _)) (andM_sameKernel (sameKernel_branch _ _) (sameKernel_branch _ _))))
  | with_reducible exact of_view (kernel (andM_sameKernel (sameKernel_branch _ _) (sameKernel_branch _ _)))
  | exact of_view (kernel (sameKernel_branch _ _))
  | exact of_view (kernel (hiddenClock64_sameKernel _))
  | exact of_view (kernel (condResched_sameKernel _))
  | exact of_view (kernel Cookies.loadPhase_sameKernel)
  | exact of_view (cookie_material _ (cookieValidatePacket_sameCookieKernel _ _ _))
  | exact of_view (modifyDev_material _ (fun _ => rfl))
  | exact of_view (kernel (by intro w x v hr; cases hr; rfl))
  | exact of_view (kernel (by intro w x v hr; cases hr)))

macro "support_focused" : tactic => `(tactic| first
  | (support_at "Origins.localSession"; exact ⟨Appends.focus _ _ _, session _⟩)
  | (support_at "modifyPeerKeysPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (modifyPeerKeysPrefix_erases _ _) (of_view (modifyPeer_material _ _))⟩)
  | (support_at "createResponsePrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (createResponsePrefix_erases _) (of_view (createResponse_material _))⟩)
  | (support_at "addMacToPacketPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (addMacToPacketPrefix_erases _ _) (of_view (addMacToPacket_material _ _))⟩)
  | (support_at "sendBufferToPeerPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (sendBufferToPeerPrefix_erases _ _) (of_view (sendBufferToPeer_material _ _))⟩)
  | (support_at "timersSessionDerivedPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (timersSessionDerivedPrefix_erases _) (of_view (timersSessionDerived_material _))⟩)
  | (support_at "timersTraversalPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (timersTraversalPrefix_erases _) (of_view (timersTraversal_material _))⟩)
  | (support_at "timersAnyAuthenticatedPacketSentPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (timersAnyAuthenticatedPacketSentPrefix_erases _) (of_view (timersAnyAuthenticatedPacketSent_material _))⟩)
  | (support_at "sendHandshakeCookiePrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (sendHandshakeCookiePrefix_erases _ _) (of_view (cookieSend_material _ _))⟩)
  | (support_at "consumeInitiationPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (consumeInitiationPrefix_erases _) (consumeInitiation_material _)⟩)
  | (support_at "consumeResponsePrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (consumeResponsePrefix_erases _) (consumeResponse_material _)⟩)
  | (support_at "setPeerEndpointFromSkbPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (setPeerEndpointFromSkbPrefix_erases _ _) (of_view (endpoint_material _ _))⟩)
  | (support_at "timersHandshakeCompletePrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (timersHandshakeCompletePrefix_erases _ _) (of_view (timersHandshakeComplete_material _ _))⟩)
  | (support_at "sendKeepalivePrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (sendKeepalivePrefix_erases _) (sendKeepalive_material _)⟩)
  | (support_at "timersAnyAuthenticatedPacketReceivedPrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (timersAnyAuthenticatedPacketReceivedPrefix_erases _) (of_view (timersAnyAuthenticatedPacketReceived_material _))⟩)
  | (support_at "peerPutMixed"; exact ⟨Appends.focus _ _ _, origin_life _ _ (peerPutMixed_erases _) (of_view (peerPut_material _))⟩)
  | (support_at "cookieMessageConsumePrefix"; exact ⟨Appends.focus _ _ _, origin_life _ _ (cookieMessageConsumePrefix_erases _) (cookieMessageConsume_material _)⟩)
  | (support_at "liftPrefix"; with_reducible apply focused_lift; support_material)
  | (support_at "Pure.pure"; with_reducible exact focused_pure _ _ _)
  | (support_at "Bind.bind"; with_reducible apply focused_bind _ _ HistoryAdapters.decode_encode)
  | (support_at "ite"; with_reducible apply focused_ite)
  | (support_append_goal; support_appends)
  | support_intro
  | with_reducible split)

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
  have hp : Focused rxEncode rxDecode RxOrigin.prepare := by
    unfold RxOrigin.prepare RxOrigin.prepareWith
    repeat' first
      | (support_at "RxOrigin.decrypt"; exact ⟨Appends.receiptObserved (Appends.focus _ _ _), rx_decrypt _⟩)
      | (support_at "setRxSkbPrefix"; exact ⟨Appends.focus _ _ _, rx_life _ _ (setRxSkbPrefix_erases _ _) (of_view (setRxSkb_material _ _))⟩)
      | (support_at "RxWorkers.publishPrefix"; exact ⟨Appends.focus _ _ _, rx_life _ _ (RxWorkers.publish_erases _ _) (of_view (publish_material _ _))⟩)
      | (support_at "liftPrefix"; with_reducible apply focused_lift; support_material)
      | (support_at "Pure.pure"; with_reducible exact focused_pure _ _ _)
      | (support_at "Bind.bind"; with_reducible apply focused_bind _ _ rx_decode_encode)
      | (support_at "ite"; with_reducible apply focused_ite)
      | support_intro
      | with_reducible split
  apply congr hp.2
  intro w h
  exact (focus_compose _ _ _ _ _ w h).symm


theorem receiveIteration : Preserves HistoryAdapters.receiveIteration :=
  workerIterPrefix_preserves _ _ safe receiveStep (lift_kernel _ (condResched_sameKernel _))

private theorem pending_material : RetainsCall RxNapi.pendingSource :=
  of_view (kernel (sameKernel_bind getDev_sameKernel (fun _ => sameKernel_pure _)))
private theorem scheduled_material : RetainsCall RxNapi.scheduledSource :=
  of_view (kernel (sameKernel_bind getDev_sameKernel (fun _ => sameKernel_pure _)))

theorem napiSoftirq : Preserves RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves safe (fun _ _ _ he hi => hi.kernel he)
    (mixed _ _ RxNapi.pending_erases pending_material) poll

theorem pollScheduledInline : Preserves RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves safe (fun _ _ _ he hi => hi.kernel he)
    (mixed _ _ RxNapi.pending_erases pending_material) poll

theorem napiIrqExit : Preserves RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves safe (fun _ _ _ he hi => hi.kernel he)
    (mixed _ _ RxNapi.scheduled_erases scheduled_material) napiSoftirq

private theorem encryptTail_material : RetainsCall RxWorkers.encryptTailSource :=
  encryptIter_material _ _ _ actualChecksum_material
    (of_view (kernel (sameKernel_pure _))) (of_view (kernel (condResched_sameKernel _)))

private theorem pendingNapi_material (next : Option Nat) : RetainsCall (pendingNapi next) :=
  of_view (kernel (sameKernel_bind getDev_sameKernel (fun _ => sameKernel_pure _)))

theorem source_get : SameKernel (get : M World) := by
  intro w x v hr
  cases hr
  rfl

theorem source_modify (f : World → World) (hf : ∀ w, (f w).k = w.k) : SameKernel (modify f) := by
  intro w x v hr
  cases hr
  exact hf w

theorem source_throw (α : Type) (e : Stop) : SameKernel (throw e : M α) := by
  intro w x v hr
  cases hr

theorem mixed_lift (a : M α) (ha : RetainsCall a) : Preserves (RxHistory.mixed (liftPrefix a)) :=
  mixed _ _ (erasesPrefix_lift a) ha

theorem mixed_throw (α : Type) (e : Stop) : Preserves (RxHistory.mixed (throw e : MixedM α)) :=
  mixed _ _ (erasesPrefix_throw e) (of_view (kernel (source_throw α e)))

macro "support_kernel" : tactic => `(tactic| first
  | with_reducible exact source_get
  | with_reducible exact source_modify _ (fun _ => rfl)
  | with_reducible exact source_throw _ _
  | (intro w x v hr; simp [invariant,unsupported] at hr)
  | with_reducible exact getDev_sameKernel
  | with_reducible exact getK_sameKernel
  | with_reducible exact sameKernel_branch _ _
  | with_reducible exact hidden_sameKernel _
  | with_reducible exact condResched_sameKernel _
  | with_reducible exact peekHiddenSite_sameKernel
  | with_reducible exact recordBudget_sameKernel
  | with_reducible exact budgetExhausted_sameKernel _
  | with_reducible exact peekUnit_sameKernel _
  | with_reducible exact resolveUnit_sameKernel _ _ _
  | (intro w x v hr; cases hr; rfl)
  | (intro w x v hr; cases hr))

macro "support_steps" : tactic => `(tactic|
  first
    | with_reducible exact mixed_lift _ (of_view (kernel source_get))
    | with_reducible exact mixed_lift _ (of_view (kernel (source_modify _ (fun _ => rfl))))
    | with_reducible exact mixed_lift _ (invariant_material _ _)
    | with_reducible exact mixed_throw _ _
    | with_reducible exact lift_retains _ (invariant_material _ _)
    | with_reducible exact lift_retains _ (unsupported_material _ _)
    | with_reducible exact lift_kernel _ source_get
    | with_reducible exact lift_kernel _ (source_modify _ (fun _ => rfl))
    | with_reducible exact prepare
    | with_reducible exact receiveIteration
    | with_reducible exact mixed _ _ (peerPutMixed_erases _) (of_view (peerPut_material _))
    | with_reducible exact mixed _ _ (getPeerMixed_erases _) (of_view (getPeer_material _))
    | with_reducible exact mixed _ _ (getTxSkbPrefix_erases _) (of_view (getTxSkb_material _))
    | with_reducible exact mixed _ _ (activationOccupancyPrefix_erases _) (of_view (kernel (activationOccupancy_sameKernel _)))
    | with_reducible exact mixed _ _ (activationHasWorkPrefix_erases _) (of_view (kernel (activationHasWork_sameKernel _)))
    | with_reducible exact mixed _ _ (pendingNapiPrefix_erases _) (pendingNapi_material _)
    | with_reducible exact mixed _ _ (txIterPrefix_erases _ (erasesPrefix_lift _)) (actualTxIter_material _)
    | (with_reducible apply mixed _ _ (erasesPrefix_lift _); first
        | with_reducible exact of_view (modifyDev_material _ (fun _ => rfl))
        | (apply of_view; apply kernel; support_kernel))
    | (with_reducible apply mixed _ _ (erasesPrefix_throw _); apply of_view; apply kernel; intro w x v hr; cases hr)
    | (with_reducible apply lift_kernel; support_kernel)
    | with_reducible exact PrefixPreserves.pure safe _
    | with_reducible apply PrefixPreserves.range _ _ _ safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq,Prod.mk.injEq,reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

theorem encryptIteration : Preserves RxHistory.encryptIteration :=
  PrefixPreserves.bind napiSoftirq (fun _ => mixed _ _ RxWorkers.encryptTail_erases encryptTail_material)

theorem decryptStep : Preserves RxHistory.decryptStep := by
  unfold RxHistory.decryptStep RxWorkers.decryptWith
  repeat' first
    | with_reducible exact napiSoftirq
    | with_reducible exact napiIrqExit
    | support_steps

theorem decryptIteration : Preserves RxHistory.decryptIteration := by
  apply workerIterPrefix_preserves _ _ safe decryptStep
  exact PrefixPreserves.bind (lift_kernel _ (condResched_sameKernel _))
    (fun _ => lift_kernel _ (sameKernel_branch _ _))

theorem cryptAhead (pid : PeerId) : Preserves (RxHistory.cryptAhead pid) := by
  unfold RxHistory.cryptAhead
  repeat' first | with_reducible exact encryptIteration | support_steps

theorem activationIteration (a : Activation) : Preserves (RxHistory.activationIteration a) := by
  unfold RxHistory.activationIteration
  repeat' first
    | with_reducible exact encryptIteration
    | with_reducible exact decryptIteration
    | with_reducible exact cryptAhead _
    | support_steps

theorem activationRun (a : Activation) : Preserves (RxHistory.activationRun a) := by
  unfold RxHistory.activationRun
  repeat' first | with_reducible exact activationIteration _ | support_steps

theorem dispatch (worker : Worker) : Preserves (RxHistory.dispatch worker) := by
  unfold RxHistory.dispatch
  repeat' first | with_reducible exact activationRun _ | support_steps

/-- The actual saved probe is checked before the copied-world filter executes.
No receipt from a copied trial is claimed to occur in this committed journal. -/
theorem schedule (stack : Option Worker) : Preserves (RxHistory.schedule stack) := by
  unfold RxHistory.schedule
  simp only [List.find?_cons,List.find?_nil]
  repeat' first
    | with_reducible exact dispatch _
    | with_reducible exact activationRun _
    | with_reducible exact napiSoftirq
    | with_reducible exact filter_probe
    | support_steps

theorem nestedResched (self : Worker) : Preserves (RxHistory.nestedResched self) := by
  unfold RxHistory.nestedResched
  apply PrefixPreserves.bind (lift_kernel _ (condResched_sameKernel _))
  intro b
  split
  · exact schedule _
  · exact PrefixPreserves.pure safe _

end Leanux.Proofs.WG.Origins.HistorySupport
