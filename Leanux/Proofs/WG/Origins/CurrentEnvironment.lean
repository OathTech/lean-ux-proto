import Leanux.Proofs.WG.Origins.CurrentWorkers

/-! Current identity and positional checks through the actual activation and
scheduler observers. Copied filter trials stay outside the committed journal;
all source Stops and arbitrary incoming histories remain in scope. -/
namespace Leanux.Proofs.WG.CurrentEnvironment
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues CurrentLifecycle CurrentTraffic ConfiguredHandshake
open Origins hiding Inv

private theorem sendSkb_view (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    SameView ConfiguredIdentity.view (sendSkbToPeer pid bytes ds) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4; exact (send4_view _ _ _ _ _).wp (fun s => s = initial))
    | (rx_retention_head send6; exact (send6_view _ _ _ _ _).wp (fun s => s = initial))
    | configured_step initial

private theorem dataSent_view (pid : PeerId) : SameView ConfiguredIdentity.view (timersDataSent pid) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold timersDataSent
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head callerJiffies
       exact ((callerJiffies_sameWGWorld _).factor ConfiguredIdentity.view).wp (fun s => s = initial))
    | (rx_retention_head jitterBelowRekeyTimeout
       exact ((jitterBelowRekeyTimeout_sameWGWorld _).factor ConfiguredIdentity.view).wp (fun s => s = initial))
    | (rx_retention_head modPeerTimerGuard
       exact (ConfiguredIdentity.modPeerTimerGuard_view _).wp (fun s => s = initial))
    | (rx_retention_head armTimer
       exact (ConfiguredIdentity.armTimer_view _ _ _ _).wp (fun s => s = initial))
    | configured_step initial

private theorem fresh_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (keepKeyFresh pid) := by
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation
       exact sendQueuedHandshakeInitiation_preserves _ _ history)
    | current_traffic_step history

private theorem complete_preserves (pid : PeerId) (item : List SkbId)
    (history : List SessionOrigin.Receipt) : Preserves (Inv history) (createDataDone pid item) := by
  let P := Inv history
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by current_skb_step history
  have traversal : Preserves P (timersTraversal pid) :=
    current_preserves _ (ConfiguredIdentity.timersTraversal_view _) (Retaining.of_view (Retaining.timersTraversal_material _)) history
  have authenticated : Preserves P (timersAnyAuthenticatedPacketSent pid) :=
    current_preserves _ (ConfiguredIdentity.timersAnyAuthenticatedPacketSent_view _)
      (Retaining.of_view (Retaining.timersAnyAuthenticatedPacketSent_material _)) history
  have send (bytes : List UInt8) (ds : Nat) : Preserves P (sendSkbToPeer pid bytes ds) :=
    current_preserves _ (sendSkb_view _ _ _) (Retaining.of_view (Retaining.sendSkbToPeer_material _ _ _)) history
  have dataSent : Preserves P (timersDataSent pid) :=
    current_preserves _ (dataSent_view _) (Retaining.of_view (Retaining.timersDataSent_material _)) history
  have fresh : Preserves P (keepKeyFresh pid) := fresh_preserves _ history
  routing_tx_source [createDataDone] using [traversal,authenticated,send,dataSent,fresh,skb,ambient]

private theorem txStep_preserves (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (txStep pid) := by
  rw [← TxDisposition.stepSource_eq]
  let P := Inv history
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have skb {α : Type} (a : SkbM α) : Preserves P (liftSkb a) := by current_skb_step history
  have complete (item : List SkbId) : Preserves P (createDataDone pid item) := complete_preserves _ _ history
  have key (kp : Option KeypairId) : Preserves P (keypairPut kp false) := by current_traffic_step history
  have put : Preserves P (peerPut (some pid)) := by current_traffic_step history
  have dispose (item : List SkbId) (kp : KeypairId) : Preserves P (TxDisposition.disposeSource pid item kp) := by
    routing_tx_source [TxDisposition.disposeSource] using [skb,key,put]
  have update (f : Peer → Peer) (hf : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p) :
      Preserves P (do let p ← getPeer pid; setPeer pid (f p)) :=
    current_preserves _ (ConfiguredIdentity.modifyPeer_view pid f hf)
      (Retaining.of_view (Retaining.modifyPeer_material pid f)) history
  have drop : Preserves P (do let p ← getPeer pid; setPeer pid {p with txQueue := p.txQueue.dropPeeked}) :=
    update _ (fun _ => rfl)
  have body (first : Option (List SkbId)) : Preserves P (TxDisposition.bodySource pid first) := by
    unfold TxDisposition.bodySource
    simp only [getPeer_twice]
    apply preserves_bind
    · routing_tx_source [WG.andM] using [skb,ambient]
    · intro go
      cases go with
      | false => exact preserves_pure false
      | true =>
        simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
        cases first with
        | none => exact ambient (AmbientM.invariant "unreachable")
        | some item =>
          cases hh : item.head? with
          | none => simp only [hh]; exact ambient (AmbientM.invariant "an empty ring item")
          | some headId =>
            simp only [hh]
            apply preserves_bind (skb (SkbStore.getTx headId))
            intro head
            apply preserves_bind drop
            intro _
            routing_tx_source [] using [complete,dispose,ambient]
  unfold TxDisposition.stepSource
  apply preserves_bind (show Preserves P (getPeer pid) from by current_traffic_step history)
  intro p
  apply preserves_bind
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.native_store)
      _ (prevQueuePeek_sameWGStore p.txQueue) history)
  intro out
  rcases out with ⟨first,queue⟩
  exact preserves_bind (update (fun p => {p with txQueue := queue}) (fun _ => rfl)) (fun _ => body first)

private theorem txIter_preserves (pid : PeerId) (need : Leanux.M Bool)
    (hn : ∀ history, Preserves (fun w : World => Inv history w.wg) need)
    (history : List SessionOrigin.Receipt) : Preserves (fun w : World => Inv history w.wg) (txIter pid need) := by
  let P := fun w : World => Inv history w.wg
  have step : Preserves P (monadLift (txStep pid) : Leanux.M Bool) :=
    CurrentHistory.native_product _ (txStep_preserves pid) history
  have needSpec : Preserves P need := hn history
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  routing_tx_source [txIter,workerIter] using [step,needSpec,ambient]

private theorem safe (h : List RxHistory.Event) (w : World) (hi : CurrentChecks.Inv h w) :
    CurrentChecks.Safe h :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.safe) h w hi

private theorem mixed (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (he : ErasesPrefix g a) (hm : Retaining.ProductRetainsCall a)
    (hc : ∀ history, Preserves (fun w : World => Inv history w.wg) a) :
    CurrentChecks.Preserves (RxHistory.mixed g) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.mixed) g a he hm hc

private theorem native_mixed (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (he : ErasesStatePrefix g a) (hm : Retaining.RetainsCall a)
    (hc : ∀ history, Preserves (Inv history) a) :
    CurrentChecks.Preserves (RxHistory.mixed (liftWGObserver g)) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.native_mixed) g a he hm hc

private theorem product_store (a : Leanux.M α) (frame : SameProductStore a)
    (history : List SessionOrigin.Receipt) : Preserves (fun w : World => Inv history w.wg) a :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.product_store) a frame history

private theorem mixed_store (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (he : ErasesPrefix g a) (frame : SameProductStore a) :
    CurrentChecks.Preserves (RxHistory.mixed g) :=
  mixed g a he (Retaining.of_view (Origins.kernel (project := id) frame)) (product_store a frame)

private theorem lift_store (a : Leanux.M α) (frame : SameProductStore a) :
    CurrentChecks.Preserves (liftPrefix a) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.lift_store) a frame

private theorem txIteration (pid : PeerId) :
    CurrentChecks.Preserves (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  mixed _ _ (txIterPrefix_erases _ (erasesPrefix_lift _)) (Retaining.actualTxIter_material pid)
    (txIter_preserves pid _ (product_store _ (condResched_sameKernel _)))

private theorem pending (next : Option Nat) :
    CurrentChecks.Preserves (RxHistory.mixed (pendingNapiPrefix next)) := by
  apply mixed_store _ _ (pendingNapiPrefix_erases next)
  unfold pendingNapi
  exact SameView.bind (liftWG_sameProductStore getDev getDev_sameWGStore) (fun _ => SameView.pure _ _)

open Lean Meta Elab Tactic in
elab "current_env_at " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``CurrentChecks.Preserves || target.isAppOf ``PrefixPreserves do
    throwError "not current checks"
  let fields := target.getAppArgs
  unless fields.size > 0 do throwError "missing observer"
  let mut action := fields.back!.consumeMData
  for wrapper in [``RxHistory.mixed,``liftWGObserver] do
    if action.isAppOf wrapper then
      let parts := action.getAppArgs
      unless parts.size > 0 do throwError "missing wrapped observer"
      action := parts.back!.consumeMData
  action := action.headBeta
  let expected ← realizeGlobalConstNoOverloadWithInfo wanted
  if expected != ``liftPrefix && action.isAppOf ``liftPrefix then
    let parts := action.getAppArgs
    unless parts.size > 0 do throwError "missing lifted action"
    action := parts.back!.consumeMData
    if action.isAppOf ``liftWG then
      let fields := action.getAppArgs
      unless fields.size > 0 do throwError "missing native action"
      action := fields.back!.consumeMData
  unless action.getAppFn.constName? == some expected do throwError "different observer head"

open Lean Meta Elab Tactic in
elab "current_env_match" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``CurrentChecks.Preserves || target.isAppOf ``PrefixPreserves do
    throwError "not current checks"
  let fields := target.getAppArgs
  unless fields.size > 0 do throwError "missing observer"
  let action := fields.back!.consumeMData
  let some _ ← matchMatcherApp? action | throwError "not observer matcher"
  replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)

macro "current_env_steps" : tactic => `(tactic| first
  | (current_env_at HistoryAdapters.receiveIteration; exact CurrentReceiveChecks.receiveIteration)
  | (current_env_at getPeerMixed
     apply native_mixed _ _ (getPeerMixed_erases _) (Retaining.of_view (Retaining.getPeer_material _))
     intro history; current_traffic_step history)
  | (current_env_at getTxSkbPrefix
     apply native_mixed _ _ (getTxSkbPrefix_erases _)
     · support_native_material
     · intro history; unfold getTxSkb; current_skb_step history)
  | (current_env_at activationOccupancyPrefix
     exact mixed_store _ _ (activationOccupancyPrefix_erases _) (activationOccupancy_sameKernel _))
  | (current_env_at activationHasWorkPrefix
     exact mixed_store _ _ (activationHasWorkPrefix_erases _) (activationHasWork_sameKernel _))
  | (current_env_at pendingNapiPrefix; exact pending _)
  | (current_env_at txIterPrefix; exact txIteration _)
  | (current_env_at liftWGPrefix
     apply native_mixed _ _ (erasesStatePrefix_lift _)
     · support_native_material
     · intro history; repeat' current_lifecycle_step history)
  | (current_env_at getDev; exact lift_store _ (liftWG_sameProductStore getDev getDev_sameWGStore))
  | (current_env_at liftPrefix
     first
     | apply mixed_store _ _ (erasesPrefix_lift _)
     | apply lift_store
     simp only [getAmbient,hidden,peekHiddenSite,recordBudget,budgetExhausted,peekUnit,
       resolveUnit,modifyAmbient,invariant,unsupported]
     intro initial
     exact productAmbient_spec _ _ (fun _ _ hi => hi))
  | (current_env_at throw
     exact mixed_store _ _ (erasesPrefix_throw _) (HistorySupport.source_throw _ _))
  | (current_env_at Pure.pure; exact PrefixPreserves.pure safe _)
  | (current_env_at ForIn.forIn; first
      | apply PrefixPreserves.range (State := World) _ _ _ safe
      | apply PrefixPreserves.forIn _ _ _ safe)
  | (current_env_at Bind.bind; apply PrefixPreserves.bind)
  | (current_env_at ite; split)
  | current_env_match
  | support_intro)

theorem cryptAhead (pid : PeerId) : CurrentChecks.Preserves (RxHistory.cryptAhead pid) := by
  unfold RxHistory.cryptAhead
  repeat' first
    | (current_env_at RxHistory.encryptIteration; exact CurrentWorkers.encryptIteration)
    | current_env_steps

theorem activationIteration (a : Activation) : CurrentChecks.Preserves (RxHistory.activationIteration a) := by
  unfold RxHistory.activationIteration
  repeat' first
    | (current_env_at RxHistory.encryptIteration; exact CurrentWorkers.encryptIteration)
    | (current_env_at RxHistory.decryptIteration; exact CurrentWorkers.decryptIteration)
    | (current_env_at RxHistory.cryptAhead; exact cryptAhead _)
    | current_env_steps

theorem activationRun (a : Activation) : CurrentChecks.Preserves (RxHistory.activationRun a) := by
  unfold RxHistory.activationRun
  repeat' first
    | (current_env_at RxHistory.activationIteration; exact activationIteration _)
    | current_env_steps

theorem dispatch (worker : Worker) : CurrentChecks.Preserves (RxHistory.dispatch worker) := by
  unfold RxHistory.dispatch
  repeat' first
    | (current_env_at RxHistory.activationRun; exact activationRun _)
    | current_env_steps

theorem schedule (stack : Option Worker) : CurrentChecks.Preserves (RxHistory.schedule stack) := by
  unfold RxHistory.schedule
  simp only [List.find?_cons,List.find?_nil]
  repeat' first
    | (current_env_at RxHistory.dispatch; exact dispatch _)
    | (current_env_at RxHistory.activationRun; exact activationRun _)
    | (current_env_at RxHistory.napiSoftirq; exact CurrentWorkers.napiSoftirq)
    | (current_env_at RxHistory.audit; exact CurrentChecks.filter_probe)
    | current_env_steps

theorem nestedResched (self : Worker) : CurrentChecks.Preserves (RxHistory.nestedResched self) := by
  unfold RxHistory.nestedResched
  apply PrefixPreserves.bind (lift_store _ (condResched_sameKernel _))
  intro b
  split
  · exact schedule _
  · exact PrefixPreserves.pure safe _

end Leanux.Proofs.WG.CurrentEnvironment
