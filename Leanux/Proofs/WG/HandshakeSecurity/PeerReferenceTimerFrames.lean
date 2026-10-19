import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceTrafficFrames
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveTimerFrames

/-! Native wheel operations retain positive resident references. Saved timer
records carry their original positive count through recorded clock choices. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem place_on_wheel (pid : PeerId) (t : PeerTimer) (expires clk : UInt64)
    (unit : Option Nat) :
    Framing.Preserves Inv (placeOnWheel pid t expires clk unit) := by
  let P := Inv
  let R := fun (p : Peer) (w : WGWorld) =>
    P w ∧ 0 < p.refcount
  have hg : Hoare (getPeer pid) P (fun p => R p) :=
    read_saved pid
  have peerRead : Framing.Preserves P (getPeer pid) :=
    hoare_consequence hg (fun _ h => h) (fun _ _ h => h.1)
  have setter (p q : Peer) (hc : q.refcount = p.refcount) :
      Hoare (setPeer pid q) (R p) (fun _ => P) := write_cell pid p q hc
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
    : Framing.Preserves Inv (armTimer pid timer delay jc) := by
  unfold armTimer
  simp (config := {zeta := false}) only [getAmbient,hidden,invariant,unsupported]
  repeat' first
    | rxstack_preserves_join
    | (rx_retention_head placeOnWheel; exact place_on_wheel _ _ _ _ _)
    | peer_reference_traffic_step

theorem del_timer (pid : PeerId) (timer : PeerTimer) :
    Framing.Preserves Inv (delTimer pid timer) :=
  update_peer pid (fun p => (p.setTimer timer none).setWheel timer none)
    (by intro p positive; cases timer <;> exact positive)

theorem mod_guard (pid : PeerId) :
    Framing.Preserves Inv (modPeerTimerGuard pid) := by
  unfold modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' peer_reference_traffic_step

theorem mod_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    : Framing.Preserves Inv (modPeerTimer site pid timer delay) := by
  unfold modPeerTimer
  apply preserves_bind (world (callerJiffies_sameWGWorld site))
  intro jc
  apply preserves_bind (mod_guard pid)
  intro ready
  split
  · exact preserves_bind (arm_timer pid timer delay jc) (fun _ => preserves_pure _)
  · exact preserves_pure _

macro "peer_reference_timer_step" : tactic => `(tactic| first
  | (rx_retention_head delTimer; exact del_timer _ _)
  | (rx_retention_head modPeerTimer; exact mod_timer _ _ _ _)
  | (rx_retention_head modPeerTimerGuard; exact mod_guard _)
  | (rx_retention_head armTimer; exact arm_timer _ _ _ _)
  | (rx_retention_head callerJiffies; exact world (callerJiffies_sameWGWorld _))
  | (rx_retention_head jitterBelowRekeyTimeout; exact world (jitterBelowRekeyTimeout_sameWGWorld _))
  | peer_reference_traffic_step)

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
