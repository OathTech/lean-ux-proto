import Leanux.Proofs.WG.Queues.RxReservationPayment
import Leanux.Proofs.WG.Origins.ConfiguredHandshake
import Leanux.Proofs.WG.Queues.WorkQueueFrames

/-! Source frames for handshake-send work, followed by payment of its supplied
reservation. Pending flags and queue membership do not manufacture credit.
Every contract keeps the actual native Ambient endpoints and normal outcomes. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.SendWork
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private abbrev Cell := Nat × Nat × PrevQueue SkbId × Bool × Option KeypairId
private def cell (p : Peer) : Cell :=
  (p.internalId,p.refcount,p.rxQueue,p.napiScheduled,p.keypairCurrent)
private structure State where
  epoch : Nat
  ring : PtrRing SkbId
  packets : SkbId → Option RxPacket
  keys : KeypairId → Option Keypair
  peers : PeerId → Option Cell
  sendQueue : List PeerId
  clearQueue : List PeerId
private def state (d : Device) : State :=
  ⟨d.ifindex,d.decryptQueue,fun id => d.rxSkbs[id]?,fun id => d.keypairs[id]?,
    (fun pid => d.peers[pid]?.map cell),d.sendWorkQueue,d.clearWorkQueue⟩
private def view (w : WGWorld) : Option State := w.dev.map state

private theorem state_peer_same (d : Device) (pid : PeerId) (old p : Peer)
    (hp : d.peers[pid]? = some old) (he : cell p = cell old) :
    state {d with peers := d.peers.insert pid p} = state d := by
  unfold state
  congr 1
  funext q
  by_cases h : pid = q
  · subst q; simp [hp,he]
  · simp [Std.TreeMap.getElem?_insert,h]

private theorem getPeer_spec (P : Option State → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (view w)⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜P (view w) ∧ (view w).bind (fun s => s.peers pid) = some (cell p)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi hr
  obtain ⟨rfl,rfl,d,hd,hp⟩ := getPeer_normal pid w v p a b hr
  exact ⟨hi,by simp [view,state,hd,hp]⟩

private theorem setPeer_spec (P : Option State → Prop) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (view w) ∧ (view w).bind (fun s => s.peers pid) = some (cell p)⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜P (view w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi hr
  cases hd : w.dev with
  | none => simp [view,hd] at hi
  | some d =>
    obtain ⟨old,ho,he⟩ := Option.map_eq_some_iff.mp (by simpa [view,state,hd] using hi.2)
    cases hr
    simpa [view,setPeer,modifyDev,hd,state_peer_same d pid old p ho he.symm] using hi.1

private theorem sameWG {α : Type} {a : WG.M α} (ha : SameWGStore a) : SameView view a :=
  ha.of_factor (fun s : WGStoreView => s.dev.map state) _ (fun _ => rfl)

private theorem modifyDev_spec (P : Option State → Prop) (f : Device → Device)
    (hf : ∀ d, state (f d) = state d) :
    Preserves (fun w => P (view w)) (modifyDev f) := by
  apply hoare_modify
  intro w hi
  simpa only [view,Option.map_map,Function.comp_def,hf] using hi

private theorem placeOnWheel_view (pid : PeerId) (t : PeerTimer) (expires clk : UInt64)
    (unit : Option Nat) : SameView view (placeOnWheel pid t expires clk unit) := by
  intro s
  let P := fun w : WGWorld => view w = s
  let R := fun (p : Peer) (w : WGWorld) =>
    P w ∧ (view w).bind (fun state => state.peers pid) = some (cell p)
  have hg : Hoare (getPeer pid) P (fun p => R p) :=
    getPeer_spec (fun q => q = s) pid
  have peerRead : Preserves P (getPeer pid) :=
    hoare_consequence hg (fun _ h => h) (fun _ _ h => h.1)
  have setter (p q : Peer) (hc : cell q = cell p) :
      Hoare (setPeer pid q) (R p) (fun _ => P) := by
    apply hoare_consequence (setPeer_spec (fun r => r = s) pid q)
    · intro w h
      exact ⟨h.1, by simpa only [hc] using h.2⟩
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
    apply preserves_bind peerRead
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
      (by cases t <;> rfl))
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
          (by cases t <;> rfl))
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

private theorem armTimer_view (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (jc : Option UInt64 := none) : SameView view (armTimer pid timer delay jc) := by
  have peerRead (q : PeerId) : SameView view (getPeer q) := by
    intro s
    exact hoare_consequence (getPeer_spec (fun v => v = s) q)
      (fun _ h => h) (fun _ _ h => h.1)

  have ambient {α : Type} (a : AmbientM α) : SameView view (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => view w = initial)
  have read : SameView view (get : WG.M WGWorld) := by
    intro initial
    exact hoare_consequence (hoare_get (fun w => view w = initial))
      (fun _ h => h) (fun _ _ h => h.2)
  have dev : SameView view getDev := by
    unfold getDev
    apply SameView.bind read
    intro w
    cases w.dev with
    | none => exact ambient (AmbientM.invariant _)
    | some d => exact SameView.pure _ d
  have stopped {α : Type} (e : Stop) : SameView view (throw e : WG.M α) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hr
    cases hr
  have edit (f : WGWorld → WGWorld) (hf : ∀ w, view (f w) = view w) :
      SameView view (modify f : WG.M Unit) := by
    intro initial
    apply hoare_modify
    intro w hw
    exact (hf w).trans hw
  unfold armTimer
  simp (config := { zeta := false }) only [getAmbient, hidden, invariant, unsupported]
  repeat' first
    | rxqueue_join_let
    | rxqueue_join_use
    | (snapshot_head placeOnWheel; exact placeOnWheel_view pid _ _ _ _)
    | (snapshot_head getDev; exact dev)
    | (snapshot_head getPeer; exact peerRead _)
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

private theorem delTimer_view (pid : PeerId) (timer : PeerTimer) :
    SameView view (delTimer pid timer) := by
  intro initial
  unfold delTimer
  apply hoare_bind _ _ (getPeer_spec (fun s => s = initial) pid)
  intro p
  apply hoare_consequence (setPeer_spec (fun s => s = initial) pid _)
  · intro w h
    refine ⟨h.1, ?_⟩
    cases timer <;> exact h.2
  · exact fun _ _ h => h

private theorem modPeerTimerGuard_view (pid : PeerId) :
    SameView view (modPeerTimerGuard pid) := by
  have ambient {α : Type} (a : AmbientM α) : SameView view (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => view w = initial)
  have read : SameView view (get : WG.M WGWorld) := by
    intro initial
    exact hoare_consequence (hoare_get (fun w => view w = initial))
      (fun _ h => h) (fun _ _ h => h.2)
  have dev : SameView view getDev := by
    unfold getDev
    apply SameView.bind read
    intro w
    cases w.dev with
    | none => exact ambient (AmbientM.invariant _)
    | some d => exact SameView.pure _ d
  have peer : SameView view (getPeer pid) := by
    intro s
    exact hoare_consequence (getPeer_spec (fun v => v = s) pid)
      (fun _ h => h) (fun _ _ h => h.1)
  unfold modPeerTimerGuard
  apply SameView.bind dev
  intro d
  apply SameView.bind peer
  intro p
  unfold WG.andM
  apply SameView.bind (ambient (AmbientM.branch .modTimerRunning d.running))
  intro running
  split
  · exact ambient (AmbientM.branch .modTimerAlive !p.isDead)
  · exact SameView.pure _ _

private theorem modPeerTimer_view (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) : SameView view (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer
  apply SameView.bind ((callerJiffies_sameWGWorld site).of_factor view view (fun _ => rfl))
  intro jc
  apply SameView.bind (modPeerTimerGuard_view pid)
  intro ready
  split
  · exact SameView.bind (armTimer_view pid timer delay jc) (fun _ => SameView.pure _ _)
  · exact SameView.pure _ _

private theorem timersTraversal_view (pid : PeerId) : SameView view (timersTraversal pid) := by
  have peer : SameView view (getPeer pid) := by
    intro s
    exact hoare_consequence (getPeer_spec (fun v => v = s) pid)
      (fun _ h => h) (fun _ _ h => h.1)
  have ambient {α : Type} (a : AmbientM α) : SameView view (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => view w = initial)
  unfold timersTraversal
  apply SameView.bind peer
  intro p
  apply SameView.bind (ambient (AmbientM.branchCmp .traversalKeepalive
    (p.persistentKeepaliveInterval != 0) p.persistentKeepaliveInterval 0))
  intro nonzero
  cases nonzero with
  | false => exact SameView.pure _ _
  | true =>
    exact (modPeerTimer_view .timerJiffiesTraversal pid .persistentKeepalive
      (p.persistentKeepaliveInterval * HZ)).map (fun _ => ())

private theorem timersAnyAuthenticatedPacketSent_view (pid : PeerId) :
    SameView view (timersAnyAuthenticatedPacketSent pid) := delTimer_view pid .sendKeepalive

private theorem timersHandshakeInitiated_view (pid : PeerId) :
    SameView view (timersHandshakeInitiated pid) := by
  unfold timersHandshakeInitiated
  apply SameView.bind ((callerJiffies_sameWGWorld .timerJiffiesHandshakeInitiated).of_factor
    view view (fun _ => rfl))
  intro jc
  apply SameView.bind ((jitterBelowRekeyTimeout_sameWGWorld .retransmitJitter).of_factor
    view view (fun _ => rfl))
  intro jitter
  apply SameView.bind (modPeerTimerGuard_view pid)
  intro ready
  cases ready with
  | false => exact SameView.pure _ _
  | true => exact armTimer_view pid .retransmitHandshake (REKEY_TIMEOUT_TICKS + jitter) jc

private theorem read_bind (initial : Option State) {α : Type}
    (pid : PeerId) (f : Peer → WG.M α)
    (hf : ∀ p, initial.bind (fun s => s.peers pid) = some (cell p) →
      Preserves (fun w => view w = initial) (f p)) :
    Preserves (fun w => view w = initial) (getPeer pid >>= f) := by
  apply hoare_bind _ _ (getPeer_spec (fun s => s = initial) pid)
  intro p
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' h hr
  have saved := h.2
  rw [h.1] at saved
  exact (hoare_iff_run_ambient _ _ _).mp (hf p saved) w ambient x v ambient' h.1 hr

private theorem set_saved (initial : Option State) (pid : PeerId) (p : Peer)
    (hp : initial.bind (fun s => s.peers pid) = some (cell p)) :
    Preserves (fun w => view w = initial) (setPeer pid p) := by
  apply hoare_consequence (setPeer_spec (fun s => s = initial) pid p)
  · intro w h
    exact ⟨h, by rw [h]; exact hp⟩
  · exact fun _ _ h => h

macro "send_work_step " initial:term : tactic => `(tactic| first
  | (env_bind_head getPeer; apply read_bind $initial; intro p hp)
  | (rx_retention_head setPeer; apply set_saved $initial; assumption)
  | (rx_retention_head getPeer
     exact hoare_consequence (getPeer_spec (fun s => s = $initial) _)
       (fun _ h => h) (fun _ _ h => h.1))
  | (rx_retention_head getDev; exact (sameWG getDev_sameWGStore).wp (fun s => s = $initial))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM
     apply hoare_liftIndex
     intro w d table hi hd
     simpa only [view,hd,Option.map_some,state] using hi)
  | (allocation_release_lift_from Net.M
     exact hoare_liftRouting _ _ (fun _ _ h => h))
  | (rx_retention_head liftRouting; exact hoare_liftRouting _ _ (fun _ _ h => h))
  | (rx_retention_head getRouting
     exact hoare_liftRouting ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
       _ (fun _ _ h => h))
  | (rx_retention_head get; exact hoare_consequence (hoare_get _)
      (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head MonadStateOf.get; exact hoare_consequence (hoare_get _)
      (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head modifyDev; exact modifyDev_spec
      (fun s => s = $initial) _ (fun _ => rfl))
  | (rx_retention_head throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w ambient x v ambient' hi hr
     cases hr)
  | (rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w ambient x v ambient' hi hr
     cases hr)
  | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
  | rx_retention_step)

macro "send_work_crypto " initial:term : tactic => `(tactic| first
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => view w = $initial))
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (fun w => view w = $initial))
  | (rx_retention_head messageEphemeral; exact (messageEphemeral_sameWGWorld _ _ _ _).wp (fun w => view w = $initial))
  | (rx_retention_head mixDh; exact (mixDh_sameWGWorld _ _ _ _).wp (fun w => view w = $initial))
  | (rx_retention_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp (fun w => view w = $initial)))

private theorem createInitiation_view (pid : PeerId) : SameView view (createInitiation pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  simp (config := {zeta := false}) only [branch,hidden,invariant]
  repeat' first | send_work_crypto initial | send_work_step initial

private theorem addMacToPacket_view (pid : PeerId) (msg : List UInt8) :
    SameView view (addMacToPacket pid msg) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold addMacToPacket WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first | send_work_crypto initial | send_work_step initial

private theorem dstCacheReset_view (pid : PeerId) : SameView view (dstCacheReset pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold dstCacheReset
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' send_work_step initial

private theorem dstCacheGet_view (pid : PeerId) (gen : Nat) : SameView view (dstCacheGet pid gen) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold dstCacheGet
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' send_work_step initial

private theorem dstCacheSet_view (pid : PeerId) (src gen dev : Nat) : SameView view (dstCacheSet pid src gen dev) := by
  intro initial
  unfold dstCacheSet
  apply hoare_bind _ _ (getPeer_spec (fun s => s = initial) pid)
  intro p
  exact setPeer_spec (fun s => s = initial) pid _



private theorem tunnelXmit_view (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    SameView view ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold tunnelXmitSource
  simp (config := {zeta := false}) only [skipCut,unsupported]
  repeat' first
    | (rx_retention_head loopbackSend
       exact (sameWG (loopbackSend_kernel _ _)).wp (fun s => s = initial))
    | (rx_retention_head socketPort
       exact (sameWG (socketPort_sameStore _)).wp (fun s => s = initial))
    | send_work_step initial

private theorem send4ClearSrc_view cache : SameView view (send4ClearSrcSource cache) := by
  intro initial
  unfold send4ClearSrcSource
  change Preserves (fun w => view w = initial) _
  repeat' first
    | send_work_step initial

private theorem send4Finish_view e bytes ds exactRx route : SameView view (send4FinishSource e bytes ds exactRx route) := by
  intro initial
  unfold send4FinishSource
  change Preserves (fun w => view w = initial) _
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit; exact (tunnelXmit_view _ _ _ _ _).wp (fun t => t = initial))
    | send_work_step initial

private theorem send4RouteDone_view e cache bytes ds exactRx gen fallback rt :
    SameView view (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  intro initial
  unfold send4RouteDoneSource
  change Preserves (fun w => view w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head dstCacheSet; exact (dstCacheSet_view _ _ _ _).wp (fun t => t = initial))
    | (rx_retention_head send4FinishSource; exact (send4Finish_view _ _ _ _ _).wp (fun t => t = initial))
    | send_work_step initial

private theorem send4Retry_view e cache bytes ds exactRx gen fallback srcIf rt :
    SameView view (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  intro initial
  unfold send4RetrySource
  change Preserves (fun w => view w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact (send4ClearSrc_view _).wp (fun t => t = initial))
    | (rx_retention_head dstCacheReset; exact (dstCacheReset_view _).wp (fun t => t = initial))
    | (rx_retention_head send4RouteDoneSource; exact (send4RouteDone_view _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | send_work_step initial

private theorem send4Miss_view e cache bytes ds exactRx gen fallback saddr srcIf :
    SameView view (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  intro initial
  unfold send4MissSource
  change Preserves (fun w => view w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4ClearSrcSource; exact (send4ClearSrc_view _).wp (fun t => t = initial))
    | (rx_retention_head dstCacheReset; exact (dstCacheReset_view _).wp (fun t => t = initial))
    | (rx_retention_head send4RetrySource; exact (send4Retry_view _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | send_work_step initial

private theorem send4AfterCache_view e cache bytes ds exactRx gen saddr srcIf route :
    SameView view (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  intro initial
  unfold send4AfterCacheSource
  change Preserves (fun w => view w = initial) _
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4MissSource; exact (send4Miss_view _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | (rx_retention_head send4FinishSource; exact (send4Finish_view _ _ _ _ _).wp (fun t => t = initial))
    | send_work_step initial

private theorem send4_view e cache bytes ds exactRx : SameView view (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  intro initial
  unfold send4Source
  change Preserves (fun w => view w = initial) _
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact (dstCacheGet_view _ _).wp (fun t => t = initial))
    | (rx_retention_head send4AfterCacheSource; exact (send4AfterCache_view _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | send_work_step initial

private theorem send6_view (e : Endpoint) (cache : Option PeerId) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView view (send6 e cache bytes ds exactRx) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold send6
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head dstCacheGet; exact (dstCacheGet_view _ _).wp (fun s => s = initial))
    | (rx_retention_head dstCacheReset; exact (dstCacheReset_view _).wp (fun s => s = initial))
    | (rx_retention_head dstCacheSet; exact (dstCacheSet_view _ _ _ _).wp (fun s => s = initial))
    | (configured_pinned_head _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit
       exact (tunnelXmit_view _ _ _ _ _).wp (fun s => s = initial))
    | send_work_step initial

private theorem sendBufferToPeer_view (pid : PeerId) (bytes : List UInt8) : SameView view (sendBufferToPeer pid bytes) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head send4; exact (send4_view _ _ _ _ _).wp (fun s => s = initial))
    | (rx_retention_head send6; exact (send6_view _ _ _ _ _).wp (fun s => s = initial))
    | send_work_step initial

private theorem sendHandshakeInitiation_view (pid : PeerId) : SameView view (sendHandshakeInitiation pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold sendHandshakeInitiation
  simp (config := {zeta := false}) only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head createInitiation; exact (createInitiation_view _).wp (fun s => s = initial))
    | (rx_retention_head addMacToPacket; exact (addMacToPacket_view _ _).wp (fun s => s = initial))
    | (rx_retention_head timersTraversal; exact (timersTraversal_view _).wp (fun s => s = initial))
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact (timersAnyAuthenticatedPacketSent_view _).wp (fun s => s = initial))
    | (rx_retention_head timersHandshakeInitiated; exact (timersHandshakeInitiated_view _).wp (fun s => s = initial))
    | (rx_retention_head sendBufferToPeer; exact (sendBufferToPeer_view _ _).wp (fun s => s = initial))
    | send_work_crypto initial
    | send_work_step initial

private def carrierOf (s : Option State) :=
  ((s.map State.epoch,fun pid => (s.bind fun d => d.peers pid).map fun p =>
      (p.1,p.2.1,p.2.2.1)),
   (s.map State.epoch,fun id => s.bind fun d => d.packets id),
   (s.map State.epoch,fun kid => (s.bind fun d => d.keys kid).map (·.peer),
      fun pid => (s.bind fun d => d.peers pid).map fun p => (p.1,p.2.2.2.2)))
private def stableOf (s : Option State) :=
  (s.map (fun d => (d.epoch,d.ring)),
    (s.map State.epoch,fun id => s.bind fun d => d.packets id),
    fun pid => (s.bind fun d => d.peers pid).map fun p => (p.2.2.1,p.2.2.2.1))

private theorem carrier_factor (w : WGWorld) : carrierView w = carrierOf (view w) := by
  unfold carrierView peerView rxView keyView RxCredits.keyWords RxCredits.currentCells RxCredits.currentCell
  simp [carrierOf,view,state,cell,Option.map_map,Option.bind_map,Function.comp_def]

private theorem stable_factor (w : WGWorld) : stableView w = stableOf (view w) := by
  simp [stableView,RxRing.nativeCell,rxView,stableOf,view,state,cell,
    Option.map_map,Option.bind_map,Function.comp_def]

/-- Actual handshake construction and transmission preserve all existing
receive credits and the stable boundary, including normal no-send returns. -/
theorem initiation_preserves (pid : PeerId) :
    Preserves (fun w => CarrierState cs loans w ∧ StableRx cs w) (sendHandshakeInitiation pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (sendHandshakeInitiation_view pid) w a result v b hr
  exact ⟨hi.1.view ((carrier_factor v).trans ((congrArg carrierOf frame).trans (carrier_factor w).symm)),
    hi.2.view ((stable_factor v).trans ((congrArg stableOf frame).trans (stable_factor w).symm))⟩

/-- The worker's terminal put pays its supplied reservation once. This does
not infer ownership from a pending flag, queue entry, or spare refcount. -/
theorem worker_normal (o : Owner) (hi : CarrierState cs (o :: loans) w)
    (hs : StableRx cs w) (a b : Ambient)
    (hr : ((handshakeSendWorker o.slot).run w).run a = .ok (((),v),b)) :
    CarrierState cs loans v ∧ StableRx cs v := by
  unfold handshakeSendWorker at hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,sent,middle,hsend,hpay⟩ := hr
  cases u
  have preserved := (hoare_iff_run_ambient _ _ _).mp (initiation_preserves o.slot)
    w a () sent middle ⟨hi,hs⟩ hsend
  exact reservation_payment_stable preserved.1 preserved.2 middle b hpay

/-- Sending a handshake leaves both durable work queues unchanged, on all
actual normal branches, independently of reservation funding. -/
theorem initiation_workQueues (pid : PeerId) :
    SameView WorkQueueFrames.view (sendHandshakeInitiation pid) :=
  (sendHandshakeInitiation_view pid).of_factor
    (fun s => s.map fun d => (d.epoch,d.sendQueue,d.clearQueue))
    WorkQueueFrames.view (fun w => by
      simp only [WorkQueueFrames.view,view,state,Option.map_map,Function.comp_def])

/-- The worker's payment may remove its peer; it preserves the independent
work queue lists exactly. -/
theorem worker_workQueues (pid : PeerId) :
    SameView WorkQueueFrames.view (handshakeSendWorker pid) := by
  unfold handshakeSendWorker
  exact (initiation_workQueues pid).bind (fun _ => WorkQueueFrames.peerPut_frame (some pid))

end Leanux.Proofs.WG.Queues.RxCredits.SendWork
