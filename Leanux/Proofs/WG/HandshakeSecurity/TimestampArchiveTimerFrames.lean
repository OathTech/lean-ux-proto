import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveKeepalive

/-! Timer maintenance changes expiry/wheel state but preserves the timestamp
archive and the actual allocation frontier. Saved timer writes retain their
original peer-read witness. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 800000

theorem place_on_wheel (pid : PeerId) (t : PeerTimer) (expires clk : UInt64)
    (unit : Option Nat) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (placeOnWheel pid t expires clk unit) := by
  let P := StateInv history
  let R := fun (p : Peer) (w : WGWorld) =>
    P w ∧ Responder.SavedNativePeer pid p w
  have hg : Hoare (getPeer pid) P (fun p => R p) :=
    read_saved pid history
  have peerRead : Framing.Preserves P (getPeer pid) :=
    hoare_consequence hg (fun _ h => h) (fun _ _ h => h.1)
  have setter (p q : Peer) (hc : (q.internalId,q.latestTimestamp) = (p.internalId,p.latestTimestamp)) :
      Hoare (setPeer pid q) (R p) (fun _ => P) := write_cell pid p q hc history
  have ambient {α : Type} (a : AmbientM α) (Q : WGWorld → Prop) :
      Framing.Preserves Q (monadLift a : WG.M α) := hoare_liftAmbient a Q
  have stopped {α : Type} (e : Stop) (Q : WGWorld → Prop) (T : α → WGWorld → Prop) :
      Hoare (throw e : WG.M α) Q T := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' _ hr
    cases hr
  have read (Q : WGWorld → Prop) : Framing.Preserves Q (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get Q) (fun _ h => h) (fun _ _ h => h.2)
  have finish : Framing.Preserves P (do
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
        have edited : Framing.Preserves (R p)
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


theorem arm_timer (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64)
    (history : List TimestampReceipt) : Framing.Preserves (StateInv history) (armTimer pid timer delay jc) := by
  unfold armTimer
  simp (config := {zeta := false}) only [getAmbient,hidden,invariant,unsupported]
  repeat' first
    | rxstack_preserves_join
    | (rx_retention_head placeOnWheel; exact place_on_wheel _ _ _ _ _ history)
    | archive_traffic_step history

theorem del_timer (pid : PeerId) (timer : PeerTimer) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (delTimer pid timer) :=
  update_peer pid (fun p => (p.setTimer timer none).setWheel timer none)
    (by intro p; cases timer <;> exact ⟨rfl,rfl⟩) history

theorem mod_guard (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (modPeerTimerGuard pid) := by
  unfold modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' archive_traffic_step history

theorem mod_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (history : List TimestampReceipt) : Framing.Preserves (StateInv history) (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer
  apply preserves_bind (frame_world history _ (callerJiffies_sameWGWorld site))
  intro jc
  apply preserves_bind (mod_guard pid history)
  intro ready
  split
  · exact preserves_bind (arm_timer pid timer delay jc history) (fun _ => preserves_pure _)
  · exact preserves_pure _

macro "archive_timer_step " history:term : tactic => `(tactic| first
  | (rx_retention_head delTimer; exact del_timer _ _ $history)
  | (rx_retention_head modPeerTimer; exact mod_timer _ _ _ _ $history)
  | (rx_retention_head modPeerTimerGuard; exact mod_guard _ $history)
  | (rx_retention_head armTimer; exact arm_timer _ _ _ _ $history)
  | (rx_retention_head callerJiffies; exact frame_world $history _ (callerJiffies_sameWGWorld _))
  | (rx_retention_head jitterBelowRekeyTimeout; exact frame_world $history _ (jitterBelowRekeyTimeout_sameWGWorld _))
  | archive_traffic_step $history)

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
