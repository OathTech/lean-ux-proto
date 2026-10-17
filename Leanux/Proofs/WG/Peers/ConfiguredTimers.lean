import Leanux.Proofs.WG.Peers.ConfiguredIdentity
import Leanux.Proofs.WG.Queues.RxMaintenanceFrames

/-! Native timer maintenance preserves the configured identity fields.
Clock records, wheel guards, missing residents and all Stops remain actual. -/
namespace Leanux.Proofs.WG.ConfiguredIdentity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem placeOnWheel_view (pid : PeerId) (t : PeerTimer) (expires clk : UInt64)
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

theorem armTimer_view (pid : PeerId) (timer : PeerTimer) (delay : Nat)
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

theorem delTimer_view (pid : PeerId) (timer : PeerTimer) :
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

theorem modPeerTimerGuard_view (pid : PeerId) :
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

theorem modPeerTimer_view (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) : SameView view (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer
  apply SameView.bind ((callerJiffies_sameWGWorld site).of_factor view view (fun _ => rfl))
  intro jc
  apply SameView.bind (modPeerTimerGuard_view pid)
  intro ready
  split
  · exact SameView.bind (armTimer_view pid timer delay jc) (fun _ => SameView.pure _ _)
  · exact SameView.pure _ _

theorem timersTraversal_view (pid : PeerId) : SameView view (timersTraversal pid) := by
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

theorem timersAnyAuthenticatedPacketSent_view (pid : PeerId) :
    SameView view (timersAnyAuthenticatedPacketSent pid) := delTimer_view pid .sendKeepalive

theorem timersHandshakeInitiated_view (pid : PeerId) :
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

end Leanux.Proofs.WG.ConfiguredIdentity
