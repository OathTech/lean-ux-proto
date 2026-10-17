import Lean
import Leanux.Proofs.WG.Queues.RxQueuePrimitives
import Leanux.Proofs.Framing.WGTime
import Leanux.Proofs.WG.Keypairs.Frames.WGBase
-- Realize the shared keepKeyFreshRx matcher congruence in its source-frame
-- dependency before this module elaborates another proof over that matcher.
import Leanux.Proofs.WG.Keypairs.Frames.WGMore

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Original endpoint and timer maintenance frames. Hidden-input validation
and failures remain in the original operations; no time or ownership premise
is added to the successful-endpoint queue contracts. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

/-- Factor an actual generated continuation, retaining the current SameView
predicate and state stack. The resulting proof is checked by the kernel. -/
elab "rxqueue_join_let" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``SameView do Lean.throwError "not SameView"
  let .app property action := target | Lean.throwError "missing action"
  let .letE name ty value body _ := action.consumeMData | Lean.throwError "not a let"
  unless name.toString.startsWith "__do_jp" do Lean.throwError "not a join continuation"
  let contract ← Lean.Meta.forallTelescope ty fun args _ =>
    Lean.Meta.mkForallFVars args (.app property (Lean.mkAppN value args))
  let valueProof ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar contract
  let (continuation, next) ← Lean.Meta.withLocalDeclD name ty fun f => do
    let contract ← Lean.Meta.forallTelescope ty fun args _ =>
      Lean.Meta.mkForallFVars args (.app property (Lean.mkAppN f args))
    Lean.Meta.withLocalDeclD `rxqueue_join contract fun hf => do
      let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar (.app property (body.instantiate1 f))
      let proof ← Lean.Meta.mkLambdaFVars #[f, hf] next
      pure (proof, next.mvarId!)
  goal.assign (Lean.mkApp2 continuation value valueProof)
  Lean.Elab.Tactic.replaceMainGoal [valueProof.mvarId!, next]

elab "rxqueue_join_use" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``SameView do Lean.throwError "not SameView"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.getAppFn.isFVar do Lean.throwError "not a local continuation"
  for decl in ← Lean.getLCtx do
    if decl.userName == `rxqueue_join then
      let proof := Lean.mkAppN decl.toExpr action.getAppArgs
      if ← Lean.Meta.withReducible (Lean.Meta.isDefEq (← Lean.Meta.inferType proof) target) then
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "no continuation contract"

theorem dstCacheReset_rxQueues (pid : PeerId) : SameView rxQueues (dstCacheReset pid) := by
  have ambient {α : Type} (a : AmbientM α) : SameView rxQueues (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => rxQueues w = initial)
  have read : SameView rxQueues (get : WG.M WGWorld) := by
    intro initial
    exact hoare_consequence (hoare_get (fun w => rxQueues w = initial))
      (fun _ h => h) (fun _ _ h => h.2)
  unfold dstCacheReset
  apply SameView.bind (ambient (get : AmbientM Ambient))
  intro a
  apply SameView.bind read
  intro w
  split
  · exact SameView.pure _ _
  · apply SameView.bind (ambient (AmbientM.hiddenJiffies .dstCacheResetTs))
    intro ts
    exact modifyPeer_rxQueues pid (fun p => {p with dstCache := {p.dstCache with resetTs := ts}})
      (fun _ => rfl) (fun _ => rfl)

theorem setPeerEndpoint_rxQueues (pid : PeerId) (e : Endpoint) : SameView rxQueues (setPeerEndpoint pid e) := by
  have ambient {α : Type} (a : AmbientM α) : SameView rxQueues (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => rxQueues w = initial)
  have both (x y : WG.M Bool) (hx : SameView rxQueues x) (hy : SameView rxQueues y) :
      SameView rxQueues (WG.andM x y) := by
    unfold WG.andM
    apply SameView.bind hx
    intro b
    split
    · exact hy
    · exact SameView.pure _ _
  have endpoint (old : Option Endpoint) : SameView rxQueues (endpointEq e old) := by
    unfold endpointEq
    apply SameView.bind (both _ _ (ambient _) (both _ _ (ambient _)
      (both _ _ (ambient _) (both _ _ (ambient _) (both _ _ (ambient _) (ambient _))))))
    intro v4
    split
    · exact SameView.pure _ _
    · apply SameView.bind (both _ _ (ambient _) (both _ _ (ambient _)
        (both _ _ (ambient _) (both _ _ (ambient _) (both _ _ (ambient _) (ambient _))))))
      intro v6
      split
      · exact SameView.pure _ _
      · exact both _ _ (ambient _) (ambient _)
  have update : SameView rxQueues (do
      let p ← getPeer pid
      setPeer pid {p with endpoint := some e}
      dstCacheReset pid) := by
    simpa only [bind_assoc] using SameView.bind
      (modifyPeer_rxQueues pid (fun p => {p with endpoint := some e}) (fun _ => rfl) (fun _ => rfl))
      (fun _ => dstCacheReset_rxQueues pid)
  unfold setPeerEndpoint
  apply SameView.bind (requireNotPending_rxQueues pid "changing the endpoint")
  intro _
  apply SameView.bind (getPeer_rxQueues pid)
  intro p
  apply SameView.bind (endpoint p.endpoint)
  intro same
  apply SameView.bind (ambient (AmbientM.branch .setEndpointEq same))
  intro equal
  split
  · exact SameView.pure _ _
  · apply SameView.bind (ambient (AmbientM.branch .setEndpointV4 _))
    intro v4
    split
    · exact update
    · apply SameView.bind (ambient (AmbientM.branch .setEndpointV6 _))
      intro v6
      split
      · exact update
      · exact SameView.pure _ _

theorem armTimer_rxQueues (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    SameView rxQueues (armTimer pid timer delay jc) := by
  have wheel (t : PeerTimer) (expires clk : UInt64) (unit : Option Nat) :
      SameView rxQueues (placeOnWheel pid t expires clk unit) := by
    intro s
    let P := fun w : WGWorld => rxQueues w = s
    let R := fun p w => P w ∧ CurrentRx s pid p
    have hg : Hoare (getPeer pid) P (fun p => R p) :=
      hoare_consequence (getPeer_rx_spec (fun q => q = s) pid) (fun _ h => h)
        (fun p w h => ⟨h.1, h.1 ▸ h.2⟩)
    have setter (p q : Peer) (hs : q.internalId = p.internalId) (hq : q.rxQueue = p.rxQueue) :
        Hoare (setPeer pid q) (R p) (fun _ => P) := by
      apply hoare_consequence (setPeer_rx_spec (fun r => r = s) pid q)
      · intro w h
        refine ⟨h.1, ?_⟩
        rcases h.2 with ⟨epoch, he⟩
        refine ⟨epoch, ?_⟩
        have hw : rxQueues w = s := h.1
        simpa only [hw, hs, hq] using he
      · exact fun _ _ h => h
    have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
        Preserves Q (monadLift a : WG.M α) := hoare_liftAmbient a Q
    have stopped {α : Type} (e : Stop) (Q : WGWorld → Prop) (T : α → WGWorld → Prop) :
        Hoare (throw e : WG.M α) Q T := by
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w ambient x v ambient' _ hr
      cases hr
    have read (Q : WGWorld → Prop) : Preserves Q (get : WG.M WGWorld) :=
      hoare_consequence (hoare_get Q) (fun _ h => h) (fun _ _ h => h.2)
    have finish : Preserves P (do
        let p ← getPeer pid
        if let some what := TimerWheel.peerWheelProblem p then
          invariant s!"peer {pid}'s timers: {what}") := by
      apply preserves_bind ((getPeer_rxQueues pid).wp (fun q => q = s))
      intro p
      cases TimerWheel.peerWheelProblem p with
      | none => exact preserves_pure _
      | some what => exact ambient (AmbientM.invariant _) P
    unfold placeOnWheel
    apply hoare_bind _ _ hg
    intro p
    cases TimerWheel.place p t expires clk with
    | kept entry =>
      apply hoare_bind _ _ (setter p (p.setTimer t (some expires))
        (by cases t <;> rfl) (by cases t <;> rfl))
      intro _
      split
      · apply preserves_bind (ambient AmbientM.peekHiddenSite P)
        intro site
        split
        · exact stopped _ _ _
        · exact finish
      · exact finish
    | enqueued slot bexp =>
      let tail : WG.M Unit := do
        let lvl := TimerWheel.levelOf slot
        if !(timeAfter bexp expires && timeBeforeEq bexp (expires + (TimerWheel.LVL_GRAN lvl).toUInt64)) then
          invariant s!"a bucket expiry {bexp} outside (expires, expires + 8^{lvl}] for expires {expires}"
        let stamp := (← get).timerEnqueues + 1
        modify fun k => {k with timerEnqueues := stamp}
        setPeer pid ((p.setTimer t (some expires)).setWheel t (some ⟨slot, bexp, stamp⟩))
        let q ← getPeer pid
        if let some what := TimerWheel.peerWheelProblem q then
          invariant s!"peer {pid}'s timers: {what}"
      have ht : Hoare tail (R p) (fun _ => P) := by
        unfold tail
        dsimp only
        split
        · exact stopped _ _ _
        · apply hoare_bind _ _ (read (R p))
          intro w
          have edited : Preserves (R p)
              (modify (fun k : WGWorld => {k with timerEnqueues := w.timerEnqueues + 1}) : WG.M Unit) := by
            apply hoare_modify
            exact fun _ h => h
          apply hoare_bind _ _ edited
          intro _
          apply hoare_bind _ _ (setter p
            ((p.setTimer t (some expires)).setWheel t (some ⟨slot, bexp, w.timerEnqueues + 1⟩))
            (by cases t <;> rfl) (by cases t <;> rfl))
          intro _
          exact finish
      cases unit with
      | none => exact ht
      | some u =>
        apply hoare_bind _ _ (ambient (AmbientM.hidden .timerEnqueue) (R p))
        intro eb
        dsimp only
        split
        · exact stopped _ _ _
        · split
          · exact stopped _ _ _
          · exact ht

  have ambient {α : Type} (a : AmbientM α) : SameView rxQueues (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => rxQueues w = initial)
  have read : SameView rxQueues (get : WG.M WGWorld) := by
    intro initial
    exact hoare_consequence (hoare_get (fun w => rxQueues w = initial))
      (fun _ h => h) (fun _ _ h => h.2)
  have dev : SameView rxQueues getDev := by
    unfold getDev
    apply SameView.bind read
    intro w
    cases w.dev with
    | none => exact ambient (AmbientM.invariant _)
    | some d => exact SameView.pure _ d
  have stopped {α : Type} (e : Stop) : SameView rxQueues (throw e : WG.M α) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hr
    cases hr
  have edit (f : WGWorld → WGWorld) (hf : ∀ w, rxQueues (f w) = rxQueues w) :
      SameView rxQueues (modify f : WG.M Unit) := by
    intro initial
    apply hoare_modify
    intro w hw
    exact (hf w).trans hw
  unfold armTimer
  simp (config := { zeta := false }) only [getAmbient, hidden, invariant, unsupported]
  repeat' first
    | rxqueue_join_let
    | rxqueue_join_use
    | (snapshot_head placeOnWheel; exact wheel _ _ _ _)
    | (snapshot_head getDev; exact dev)
    | (snapshot_head getPeer; exact getPeer_rxQueues _)
    | (snapshot_head MonadLiftT.monadLift; exact ambient _)
    | (snapshot_head MonadLift.monadLift; exact ambient _)
    | (snapshot_head get; exact read)
    | (snapshot_head MonadStateOf.get; exact read)
    | (snapshot_head throw; exact stopped _)
    | (snapshot_head MonadExceptOf.throw; exact stopped _)
    | contradiction
    | keypairs_intro_forall
    | (snapshot_head Pure.pure; exact SameView.pure _ _)
    | (snapshot_head Bind.bind; apply SameView.bind)
    | (snapshot_head ite; split)
    | (snapshot_head modify; exact edit _ (fun _ => rfl))
    | snapshot_head_reduce
    | snapshot_head_match

theorem delTimer_rxQueues (pid : PeerId) (timer : PeerTimer) : SameView rxQueues (delTimer pid timer) :=
  modifyPeer_rxQueues pid (fun p => (p.setTimer timer none).setWheel timer none)
    (fun p => by cases timer <;> rfl) (fun p => by cases timer <;> rfl)

theorem modPeerTimerGuard_rxQueues (pid : PeerId) : SameView rxQueues (modPeerTimerGuard pid) := by
  have ambient {α : Type} (a : AmbientM α) : SameView rxQueues (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => rxQueues w = initial)
  have read : SameView rxQueues (get : WG.M WGWorld) := by
    intro initial
    exact hoare_consequence (hoare_get (fun w => rxQueues w = initial))
      (fun _ h => h) (fun _ _ h => h.2)
  have dev : SameView rxQueues getDev := by
    unfold getDev
    apply SameView.bind read
    intro w
    cases w.dev with
    | none => exact ambient (AmbientM.invariant _)
    | some d => exact SameView.pure _ d
  unfold modPeerTimerGuard
  apply SameView.bind dev
  intro d
  apply SameView.bind (getPeer_rxQueues pid)
  intro p
  unfold WG.andM
  apply SameView.bind (ambient (AmbientM.branch .modTimerRunning d.running))
  intro running
  split
  · exact ambient (AmbientM.branch .modTimerAlive !p.isDead)
  · exact SameView.pure _ _

theorem modPeerTimer_rxQueues (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView rxQueues (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer
  apply SameView.bind ((callerJiffies_sameWGWorld site).of_factor rxQueues rxQueues (fun _ => rfl))
  intro jc
  apply SameView.bind (modPeerTimerGuard_rxQueues pid)
  intro ready
  split
  · exact SameView.bind (armTimer_rxQueues pid timer delay jc) (fun _ => SameView.pure _ _)
  · exact SameView.pure _ _

theorem timersHandshakeComplete_rxQueues (pid : PeerId) (site : HiddenSite) :
    SameView rxQueues (timersHandshakeComplete pid site) := by
  have ambient {α : Type} (a : AmbientM α) : SameView rxQueues (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => rxQueues w = initial)
  have update := modifyPeer_rxQueues pid
    (fun p => {p with timerHandshakeAttempts := 0, sentLastminuteHandshake := false})
    (fun _ => rfl) (fun _ => rfl)
  have finish : SameView rxQueues (do
      let now ← hidden site
      let p ← getPeer pid
      setPeer pid {p with walltimeLastHandshake := now}) := by
    apply SameView.bind (ambient (AmbientM.hidden site))
    intro now
    exact modifyPeer_rxQueues pid (fun p => {p with walltimeLastHandshake := now})
      (fun _ => rfl) (fun _ => rfl)
  unfold timersHandshakeComplete
  apply SameView.bind (delTimer_rxQueues pid .retransmitHandshake)
  intro _
  simpa only [bind_assoc] using SameView.bind update (fun _ => finish)

theorem timersAnyAuthenticatedPacketReceived_rxQueues (pid : PeerId) :
    SameView rxQueues (timersAnyAuthenticatedPacketReceived pid) := delTimer_rxQueues pid .newHandshake

theorem timersDataReceived_rxQueues (pid : PeerId) : SameView rxQueues (timersDataReceived pid) := by
  have ambient {α : Type} (a : AmbientM α) : SameView rxQueues (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => rxQueues w = initial)
  have read : SameView rxQueues (get : WG.M WGWorld) := by
    intro initial
    exact hoare_consequence (hoare_get (fun w => rxQueues w = initial))
      (fun _ h => h) (fun _ _ h => h.2)
  have dev : SameView rxQueues getDev := by
    unfold getDev
    apply SameView.bind read
    intro w
    cases w.dev with
    | none => exact ambient (AmbientM.invariant _)
    | some d => exact SameView.pure _ d
  unfold timersDataReceived
  apply SameView.bind dev
  intro d
  apply SameView.bind (ambient (AmbientM.branch .timersDataReceivedRunning d.running))
  intro running
  split
  · apply SameView.bind (getPeer_rxQueues pid)
    intro p
    apply SameView.bind (ambient (AmbientM.branch .timersDataReceivedNotPending _))
    intro pending
    split
    · intro initial
      exact discard_view_spec rxQueues (fun t => t = initial) _
        ((modPeerTimer_rxQueues .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS).wp
          (fun t => t = initial))
    · exact modifyPeer_rxQueues pid (fun p => {p with timerNeedAnotherKeepalive := true})
        (fun _ => rfl) (fun _ => rfl)
  · exact SameView.pure _ _

theorem timersTraversal_rxQueues (pid : PeerId) : SameView rxQueues (timersTraversal pid) := by
  have ambient {α : Type} (a : AmbientM α) : SameView rxQueues (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => rxQueues w = initial)
  unfold timersTraversal
  apply SameView.bind (getPeer_rxQueues pid)
  intro p
  apply SameView.bind (ambient (AmbientM.branchCmp .traversalKeepalive _ p.persistentKeepaliveInterval 0))
  intro keepalive
  split
  · intro initial
    exact discard_view_spec rxQueues (fun t => t = initial) _
      ((modPeerTimer_rxQueues .timerJiffiesTraversal pid .persistentKeepalive
        (p.persistentKeepaliveInterval * HZ)).wp (fun t => t = initial))
  · exact SameView.pure _ _

/-- Queueing a handshake can release the extra peer reference. Retention
allows the original release semantics instead of requiring ownership. -/
theorem sendQueuedHandshakeInitiation_rxQueues (pid : PeerId) (retry : Bool) :
    RetainsRx (sendQueuedHandshakeInitiation pid retry) := by
  intro s
  let P := fun w : WGWorld => ResidentsRetained s (rxQueues w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have reset := (modifyPeer_rxQueues pid (fun p => {p with timerHandshakeAttempts := 0})
    (fun _ => rfl) (fun _ => rfl)).wp (ResidentsRetained s)
  have pending := (modifyPeer_rxQueues pid (fun p => {p with handshakePending := true})
    (fun _ => rfl) (fun _ => rfl)).wp (ResidentsRetained s)
  have hqueue := (modifyDev_rxQueues (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
    (fun _ => rfl) (fun _ => rfl)).wp (ResidentsRetained s)
  have scheduled : Preserves P (do
      setPeer pid { (← getPeer pid) with handshakePending := true }
      recordQueued .sendWorker pid
      modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}) := by
    simpa only [bind_assoc, recordQueued, P] using preserves_bind pending (fun _ =>
      preserves_bind (ambient (AmbientM.recordQueued .sendWorker pid)) (fun _ => hqueue))
  let tail : WG.M Unit := do
    let p ← getPeer pid
    if ← branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT (!·) then return
    if ← branch .queuedDead p.isDead then return
    peerGet pid
    if ← branch .queuedAlreadyQueued (p.handshakePending && !(← peekQueuedUnit .sendWorker pid)) then
      peerPut (some pid)
      return
    setPeer pid { (← getPeer pid) with handshakePending := true }
    recordQueued .sendWorker pid
    modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}
  have ht : Preserves P tail := by
    unfold tail
    apply preserves_bind ((getPeer_rxQueues pid).wp (ResidentsRetained s))
    intro p
    apply preserves_bind ((branchExpired_sameWGWorld .queuedNotExpired p.lastSentHandshake
      REKEY_TIMEOUT (!·)).wp P)
    intro expired
    split
    · exact preserves_pure _
    · apply preserves_bind (ambient (AmbientM.branch .queuedDead p.isDead))
      intro dead
      split
      · exact preserves_pure _
      · apply preserves_bind ((peerGet_rxQueues pid).wp (ResidentsRetained s))
        intro _
        apply preserves_bind (ambient (AmbientM.peekQueuedUnit .sendWorker pid))
        intro queued
        apply preserves_bind (ambient (AmbientM.branch .queuedAlreadyQueued (p.handshakePending && !queued)))
        intro already
        split
        · exact preserves_bind (RetainsRx.wp (peerPut_rxQueues (some pid)) s)
            (fun _ => preserves_pure _)
        · exact scheduled
  have main : Preserves P (sendQueuedHandshakeInitiation pid retry) := by
    unfold sendQueuedHandshakeInitiation
    apply preserves_bind (ambient (AmbientM.branch .queuedNotRetry !retry))
    intro notRetry
    split
    · simpa only [bind_assoc] using preserves_bind reset (fun _ => ht)
    · exact ht
  apply hoare_consequence main
  · intro w he
    change ResidentsRetained s (rxQueues w)
    rw [he]
    exact rx_retained_refl _
  · exact fun _ _ h => h

theorem keepKeyFreshRx_rxQueues (pid : PeerId) : RetainsRx (keepKeyFreshRx pid) := by
  intro s
  let P := fun w : WGWorld => ResidentsRetained s (rxQueues w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have stopped {α : Type} (e : Stop) : Preserves P (throw e : WG.M α) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' _ hr
    cases hr
  have keyTest (current : Option KeypairId) : Preserves P (do
      WG.andM (branch .rxFreshKeypair current.isSome) do
        let some id := current | invariant "unreachable"
        let k ← getKeypair id
        WG.andM (branch .rxFreshValid k.sending.isValid) do
          WG.andM (branch .rxFreshInitiator k.iAmTheInitiator) do
            branchExpired .rxFreshExpired k.sending.birthdate
              (REJECT_AFTER_TIME - KEEPALIVE_TIMEOUT - REKEY_TIMEOUT)) := by
    unfold WG.andM
    apply preserves_bind (ambient (AmbientM.branch .rxFreshKeypair current.isSome))
    intro present
    split
    · cases current with
      | none => exact stopped _
      | some id =>
        apply preserves_bind ((getKeypair_rxQueues id).wp (ResidentsRetained s))
        intro key
        apply preserves_bind (ambient (AmbientM.branch .rxFreshValid key.sending.isValid))
        intro valid
        split
        · apply preserves_bind (ambient (AmbientM.branch .rxFreshInitiator key.iAmTheInitiator))
          intro initiator
          split
          · exact (branchExpired_sameWGWorld .rxFreshExpired key.sending.birthdate
              (REJECT_AFTER_TIME - KEEPALIVE_TIMEOUT - REKEY_TIMEOUT)).wp P
          · exact preserves_pure _
        · exact preserves_pure _
    · exact preserves_pure _
  have update := (modifyPeer_rxQueues pid (fun p => {p with sentLastminuteHandshake := true})
    (fun _ => rfl) (fun _ => rfl)).wp (ResidentsRetained s)
  have main : Preserves P (keepKeyFreshRx pid) := by
    unfold keepKeyFreshRx
    apply preserves_bind ((getPeer_rxQueues pid).wp (ResidentsRetained s))
    intro p
    apply preserves_bind (ambient (AmbientM.branch .rxFreshSentLastminute p.sentLastminuteHandshake))
    intro sent
    split
    · exact preserves_pure _
    · apply preserves_bind ((getPeer_rxQueues pid).wp (ResidentsRetained s))
      intro p
      apply preserves_bind (keyTest p.keypairCurrent)
      intro send
      apply preserves_bind (ambient (AmbientM.branch .rxFreshSend send))
      intro needed
      split
      · simpa only [bind_assoc] using preserves_bind update
          (fun _ => RetainsRx.wp (sendQueuedHandshakeInitiation_rxQueues pid false) s)
      · exact preserves_pure _
  apply hoare_consequence main
  · intro w he
    change ResidentsRetained s (rxQueues w)
    rw [he]
    exact rx_retained_refl _
  · exact fun _ _ h => h

end Leanux.Proofs.WG.Queues
