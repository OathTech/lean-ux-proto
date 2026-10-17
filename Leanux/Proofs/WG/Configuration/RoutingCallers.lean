import Leanux.Proofs.WG.Configuration.RoutingPoll
import Leanux.Proofs.Logged.FocusedInvariant
import Leanux.Proofs.WG.AllowedIps.RoutingSchedulerFrames
import Leanux.Proofs.WG.Origins.CurrentEnvironment

/-! Positional routing through the original RX callers. Each focused contract
retains the actual incoming joint journal. Only the existing poll creates
consume receipts; audit and origin leaves retain their arbitrary lower actions
and require the actual source routing frame. -/
namespace Leanux.Proofs.WG.RoutingPosition.Callers
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues AllowedIps Origins

abbrev Focused (initial : FlatTable × FlatTable) (g : RxHistory.Obs α) :=
  FocusedInvariant (Inv initial) (Safe initial) RoutingJoint.Event.rx RoutingJoint.rxEvent g

theorem bind (initial : FlatTable × FlatTable) (g : RxHistory.Obs α) (f : α → RxHistory.Obs β)
    (hg : Focused initial g) (hf : ∀ x, Focused initial (f x)) : Focused initial (g >>= f) :=
  hg.bind (fun _ => rfl) hf

theorem pure (initial : FlatTable × FlatTable) (x : α) : Focused initial (Pure.pure x) :=
  FocusedInvariant.pure _ _ (fun _ _ hi => hi.safe) x

theorem lift (initial : FlatTable × FlatTable) (a : Leanux.M α)
    (frame : ProductRetainsRoutingCall a) : Focused initial (liftPrefix a) :=
  FocusedInvariant.lift _ _ a (lift_preserves initial a frame)

theorem store (initial : FlatTable × FlatTable) (a : Leanux.M α)
    (frame : SameProductStore a) : Focused initial (liftPrefix a) :=
  lift initial a (ProjectedRetainsRoutingCall.of_same
    (routing_kernel (project := World.wg) a (frame.of_factor
      (fun s : ProductStore43 => s.2.2.2) _ (fun _ => rfl))))

theorem loop {γ : Type} (initial : FlatTable × FlatTable) (xs : List γ) (first : β)
    (f : γ → β → RxHistory.Obs (ForInStep β))
    (hf : ∀ x z, Focused initial (f x z)) : Focused initial (forIn xs first f) :=
  FocusedInvariant.forIn RoutingJoint.Event.rx RoutingJoint.rxEvent (fun _ => rfl)
    (fun h w (hi : Inv initial h w) => hi.safe) xs first f hf

theorem range (initial : FlatTable × FlatTable) (r : Std.Legacy.Range) (first : β)
    (f : Nat → β → RxHistory.Obs (ForInStep β))
    (hf : ∀ x z, Focused initial (f x z)) : Focused initial (forIn r first f) :=
  FocusedInvariant.range RoutingJoint.Event.rx RoutingJoint.rxEvent (fun _ => rfl)
    (fun h w (hi : Inv initial h w) => hi.safe) r first f hf

theorem quietFocus (initial : FlatTable × FlatTable)
    (encode : E → RxHistory.Event) (decode : RxHistory.Event → Option E)
    (quiet : ∀ pre e, Checked initial pre (RoutingJoint.Event.rx (encode e)))
    (g : PrefixM E α) (a : Leanux.M α) (erases : ErasesPrefix g a)
    (frame : ProductRetainsRoutingCall a) : Focused initial (focusPrefix encode decode g) := by
  refine ⟨Appends.focus _ _ _,?_⟩
  apply combine initial _ _ (Appends.focus _ _ _)
    (RoutingJoint.rxAction_routing (focusPrefix_erases encode decode erases))
    (global_completion_lift World.wg initial a frame)
  intro w h hi
  let prior := h.filterMap RoutingJoint.rxEvent
  let lower := runPrefix g w (prior.filterMap decode)
  let suffix := lower.2.drop (prior.filterMap decode).length
  have inner : runPrefix (focusPrefix encode decode g) w prior =
      (lower.1,prior ++ suffix.map encode) := rfl
  have outer := focusPrefix_suffix RoutingJoint.Event.rx RoutingJoint.rxEvent
    (focusPrefix encode decode g) w h lower.1 (suffix.map encode) inner
  change Checks initial (runPrefix (focusPrefix RoutingJoint.Event.rx RoutingJoint.rxEvent
    (focusPrefix encode decode g)) w h).2
  rw [outer]
  apply hi.2.append
  intro pre e post position
  have member : e ∈ (suffix.map encode).map RoutingJoint.Event.rx := by rw [position]; simp
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp member
  obtain ⟨event,_,rfl⟩ := List.mem_map.mp hr
  exact quiet _ event

theorem audit (initial : FlatTable × FlatTable) (g : AuditM α) (a : Leanux.M α)
    (erases : ErasesPrefix g a) (frame : ProductRetainsRoutingCall a) :
    Focused initial (RxHistory.audit g) :=
  quietFocus initial RxHistory.Event.audit RxHistory.auditEvent (fun _ _ => True.intro) g a erases frame

theorem mixed (initial : FlatTable × FlatTable) (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (erases : ErasesPrefix g a) (frame : ProductRetainsRoutingCall a) :
    Focused initial (RxHistory.mixed g) :=
  audit initial _ a (auditFocus_erases erases) frame

theorem native_mixed (initial : FlatTable × FlatTable) (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (erases : ErasesStatePrefix g a) (frame : RetainsRoutingCall a) :
    Focused initial (RxHistory.mixed (liftWGObserver g)) :=
  mixed initial _ _ (liftWGObserver_erases erases) (RetainsRoutingCall.liftWG frame)

theorem origin (initial : FlatTable × FlatTable) (g : PrefixM Origins.Event α) (a : Leanux.M α)
    (erases : ErasesPrefix g a) (frame : ProductRetainsRoutingCall a) :
    Focused initial (HistoryAdapters.focus g) :=
  quietFocus initial _ _ (by intro pre e; cases e <;> trivial) g a erases frame

theorem poll (initial : FlatTable × FlatTable) (pid : PeerId) (budget : Nat) :
    Focused initial (RxHistory.observePoll pid budget) :=
  ⟨RxHistory.observePoll_appends pid budget,Poll.observePoll initial pid budget⟩

private theorem pending (initial : FlatTable × FlatTable) :
    Focused initial (RxHistory.mixed (liftWGObserver RxNapi.pendingPrefix)) := by
  apply native_mixed initial _ _ RxNapi.pending_erases
  apply ProjectedRetainsRoutingCall.of_same
  routing_handshake_source [RxNapi.pendingSource] using []

private theorem scheduled (initial : FlatTable × FlatTable) :
    Focused initial (RxHistory.mixed (liftWGObserver RxNapi.scheduledPrefix)) := by
  apply native_mixed initial _ _ RxNapi.scheduled_erases
  apply ProjectedRetainsRoutingCall.of_same
  routing_handshake_source [RxNapi.scheduledSource] using []

open Lean Meta Elab Tactic in
elab "routing_call_at " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Focused || target.isAppOf ``FocusedInvariant do throwError "not a routing focus"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let action := args.back!.consumeMData |>.headBeta
  let expected ← realizeGlobalConstNoOverloadWithInfo wanted
  unless action.getAppFn.constName? == some expected do throwError "different observer head"

open Lean Meta Elab Tactic in
elab "routing_call_match" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Focused || target.isAppOf ``FocusedInvariant do throwError "not a routing focus"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let action := args.back!.consumeMData
  let some _ ← matchMatcherApp? action | throwError "not an observer match"
  replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)

macro "routing_call_steps " initial:term : tactic => `(tactic| first
  | (routing_call_at liftPrefix
     apply store $initial
     simp only [branch,branchCmp,getAmbient,hidden,peekHiddenSite,recordBudget,budgetExhausted,peekUnit,
       resolveUnit,modifyAmbient,invariant,unsupported]
     intro initial
     exact productAmbient_spec _ _ (fun _ _ hi => hi))
  | (routing_call_at Pure.pure; exact pure $initial _)
  | (routing_call_at Bind.bind; apply bind $initial)
  | (routing_call_at ite; apply FocusedInvariant.ite)
  | (routing_call_at ForIn.forIn; first
      | apply range $initial
      | apply loop $initial)
  | routing_call_match
  | support_intro)

theorem runWorker (initial : FlatTable × FlatTable) (worker : Worker) (body : RxHistory.Obs Unit)
    (hb : Focused initial body) : Focused initial (runWorkerPrefix worker body) := by
  unfold runWorkerPrefix
  repeat' first | exact hb | routing_call_steps initial

theorem napiSoftirq (initial : FlatTable × FlatTable) : Focused initial RxHistory.napiSoftirq := by
  unfold RxHistory.napiSoftirq RxNapi.softirqWith
  simp only [discard,map_const,Function.comp_def,map_eq_pure_bind]
  repeat' first
    | exact pending initial
    | (routing_call_at RxHistory.observePoll; exact poll initial _ _)
    | (routing_call_at runWorkerPrefix; apply runWorker initial)
    | routing_call_steps initial

theorem pollScheduledInline (initial : FlatTable × FlatTable) : Focused initial RxHistory.pollScheduledInline := by
  unfold RxHistory.pollScheduledInline RxNapi.inlineWith
  simp only [discard,map_const,Function.comp_def,map_eq_pure_bind]
  repeat' first
    | exact pending initial
    | (routing_call_at RxHistory.observePoll; exact poll initial _ _)
    | routing_call_steps initial

theorem napiIrqExit (initial : FlatTable × FlatTable) : Focused initial RxHistory.napiIrqExit := by
  unfold RxHistory.napiIrqExit RxNapi.irqExitWith
  repeat' first
    | exact scheduled initial
    | exact napiSoftirq initial
    | (routing_call_at liftPrefix
       exact store initial chooseNapiHere (by
         apply (ProjectedAction.iff_run _ _ _).mpr
         intro w x v hr
         cases hr
         rfl))
    | routing_call_steps initial

private theorem packets_routing (a : SkbM α) : SameView routingView (liftSkb a) := by
  intro initial
  apply hoare_liftSkb a
  intro w d skb hi hd
  simpa only [id_eq,routingView,hd,Option.map_some,routingState] using hi

private theorem publish_routing (id : SkbId) (state : PacketState) :
    SameView routingView (RxWorkers.publishSource id state) := by
  routing_handshake_source [RxWorkers.publishSource,getRxSkb,setRxSkb]
    using [peerGet_routing,packets_routing]

private theorem prepare_routing : SameView routingView RxWorkers.prepareSource := by
  routing_handshake_source [RxWorkers.prepareSource,getRxSkb,setRxSkb]
    using [packets_routing,publish_routing,decryptPacket_routing,modifyDev_routing]
  all_goals rfl

theorem prepare (initial : FlatTable × FlatTable) : Focused initial HistoryAdapters.prepare :=
  origin initial _ _ HistoryAdapters.localPrepare_erases
    (RetainsRoutingCall.liftWG (ProjectedRetainsRoutingCall.of_same prepare_routing))

theorem receiveStep (initial : FlatTable × FlatTable) : Focused initial HistoryAdapters.receiveStep :=
  origin initial _ _ HistoryAdapters.localStep_erases (RetainsRoutingCall.liftWG receiveStep_routing)

theorem receiveIteration (initial : FlatTable × FlatTable) : Focused initial HistoryAdapters.receiveIteration := by
  unfold HistoryAdapters.receiveIteration workerIterPrefix
  dsimp only
  repeat' first
    | (routing_call_at HistoryAdapters.receiveStep; exact receiveStep initial)
    | (routing_call_at liftPrefix; exact store initial _ (condResched_sameKernel _))
    | routing_call_steps initial

theorem decryptStep (initial : FlatTable × FlatTable) : Focused initial RxHistory.decryptStep := by
  unfold RxHistory.decryptStep RxWorkers.decryptWith
  apply bind initial _ _ (napiSoftirq initial)
  intro _
  apply bind initial _ _ (prepare initial)
  intro result
  cases result with
  | none => exact pure initial false
  | some pid =>
    apply bind initial _ _ (napiIrqExit initial)
    intro _
    apply bind initial _ _ (native_mixed initial _ _ (peerPutMixed_erases _) (peerPut_retainsRouting _))
    intro _
    exact bind initial _ _ (napiSoftirq initial) (fun _ => pure initial true)

theorem decryptIteration (initial : FlatTable × FlatTable) : Focused initial RxHistory.decryptIteration := by
  unfold RxHistory.decryptIteration workerIterPrefix
  dsimp only
  repeat' first
    | (routing_call_at RxHistory.decryptStep; exact decryptStep initial)
    | (routing_call_at liftPrefix; exact store initial _ (condResched_sameKernel _))
    | routing_call_steps initial

private theorem encryptTail_routing (item : Option (List SkbId)) :
    ProductRetainsRoutingCall (RxWorkers.encryptTailSource item) := by
  have steps : ProductRetainsRoutingCall (RxWorkers.encryptStepTailSource item) := by
    intro before
    let P := fun w : World => RetainsRouting before (routingView w.wg)
    have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
      productAmbient_spec a P (fun _ _ hi => hi)
    have packets {α : Type} (a : SkbM α) : Preserves P (monadLift (liftSkb a) : Leanux.M α) :=
      RetainsRoutingCall.wp (RetainsRoutingCall.liftWG (ProjectedRetainsRoutingCall.of_same (packets_routing a))) before
    have encrypt (key : KeypairId) (pkt : DataPacket) : Preserves P (encryptPacket Env.checksumHelp key pkt) :=
      RetainsRoutingCall.wp (encryptPacket_routing _ actualChecksum_routing key pkt) before
    have enqueue (xs : List SkbId) (state : PacketState) : Preserves P (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
      RetainsRoutingCall.wp (RetainsRoutingCall.liftWG (enqueuePerPeerTx_routing xs state)) before
    have main : Preserves P (RxWorkers.encryptStepTailSource item) := by
      routing_tx_source [RxWorkers.encryptStepTailSource,getTxSkb,setTxSkb] using [packets,encrypt,enqueue,ambient]
    apply hoare_consequence main
    · intro w eq
      change RetainsRouting before (routingView w.wg)
      dsimp only [id_eq] at eq
      rw [eq]
      exact RetainsRouting.refl _
    · exact fun _ _ hi => hi
  apply workerIter_routing _ _ _ _ steps
  apply ProjectedRetainsRoutingCall.of_same
  exact SameView.bind
    ((condResched_sameKernel _).of_factor (fun s : ProductStore43 => s.2.2.2.dev.map routingState) _ (fun _ => rfl))
    (fun b => by intro initial; exact productAmbient_spec (AmbientM.branch .encWorkerNeedResched b) _ (fun _ _ hi => hi))

theorem encryptIteration (initial : FlatTable × FlatTable) : Focused initial RxHistory.encryptIteration := by
  unfold RxHistory.encryptIteration
  apply bind initial _ _ (native_mixed initial _ _ (erasesStatePrefix_lift _)
    (ProjectedRetainsRoutingCall.of_same
      (pinned_const _private.Leanux.Proofs.WG.AllowedIps.RoutingTxFrames.«0».Leanux.Proofs.WG.AllowedIps.encryptPoll_routing)))
  intro item
  apply bind initial _ _ (napiSoftirq initial)
  intro _
  exact mixed initial _ _ (RxWorkers.encryptTail_erases item) (encryptTail_routing item)

end Leanux.Proofs.WG.RoutingPosition.Callers
