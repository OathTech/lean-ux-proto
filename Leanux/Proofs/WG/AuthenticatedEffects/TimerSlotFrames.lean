import Leanux.Proofs.WG.AuthenticatedEffects.TimerRootClaims
import Leanux.Proofs.WG.Peers.ConfiguredTimers

/-! Frames for the timer-store projection, including peer incarnation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def view (w : WGWorld) (pid : PeerId) (timer : PeerTimer) :=
  (w.dev.bind fun d => d.peers[pid]?).map fun p => (p.internalId,p.timer timer,p.wheel timer)

def except (pid : PeerId) (timer : PeerTimer) (w : WGWorld) :=
  fun q t => if q = pid ∧ t = timer then none else view w q t

def Resident (pid : PeerId) (p : Peer) (w : WGWorld) : Prop :=
  ∃ d, w.dev = some d ∧ d.peers[pid]? = some p

private theorem read_peer (pid : PeerId) (P : WGWorld → Prop) :
    Hoare (getPeer pid) P (fun p w => P w ∧ Resident pid p w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  obtain ⟨rfl,rfl,d,hd,hp⟩ := Queues.getPeer_normal pid w v p a b run
  exact ⟨hi,d,hd,hp⟩

private theorem insert_except (pid : PeerId) (timer : PeerTimer) (w : WGWorld)
    (d : Device) (p q : Peer) (hd : w.dev = some d) (hp : d.peers[pid]? = some p)
    (same : ∀ t, t ≠ timer → (q.internalId,q.timer t,q.wheel t) = (p.internalId,p.timer t,p.wheel t)) :
    except pid timer {w with dev := some {d with peers := d.peers.insert pid q}} = except pid timer w := by
  funext target t
  by_cases selected : target = pid
  · subst target
    by_cases kind : t = timer
    · simp [except,kind]
    · simp [except,view,hd,hp,kind,same t kind]
  · have other : pid ≠ target := Ne.symm selected
    simp [except,view,hd,selected,Std.TreeMap.getElem?_insert,other]

private theorem write_peer (pid : PeerId) (timer : PeerTimer) (p q : Peer) (initial)
    (same : ∀ t, t ≠ timer → (q.internalId,q.timer t,q.wheel t) = (p.internalId,p.timer t,p.wheel t)) :
    Hoare (setPeer pid q)
      (fun w => except pid timer w = initial ∧ Resident pid p w)
      (fun _ w => except pid timer w = initial) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  obtain ⟨d,hd,hp⟩ := hi.2
  cases run
  have frame := insert_except pid timer w d p q hd hp same
  simpa only [hd,Option.map_some] using frame.trans hi.1

theorem placeOnWheel_except (pid : PeerId) (t : PeerTimer) (expires clk : UInt64)
    (unit : Option Nat) : SameView (except pid t) (placeOnWheel pid t expires clk unit) := by
  intro s
  let P := fun w : WGWorld => except pid t w = s
  let R := fun (p : Peer) (w : WGWorld) =>
    P w ∧ Resident pid p w
  have hg : Hoare (getPeer pid) P (fun p => R p) :=
    read_peer pid P
  have peerRead : Preserves P (getPeer pid) :=
    hoare_consequence hg (fun _ h => h) (fun _ _ h => h.1)
  have setter (p q : Peer)
      (hc : ∀ other, other ≠ t → (q.internalId,q.timer other,q.wheel other) =
        (p.internalId,p.timer other,p.wheel other)) :
      Hoare (setPeer pid q) (R p) (fun _ => P) := write_peer pid t p q s hc
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
      (by intro other different; cases t <;> cases other <;> first | contradiction | rfl))
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
          (by intro other different; cases t <;> cases other <;> first | contradiction | rfl))
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

theorem armTimer_except (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (jc : Option UInt64 := none) : SameView (except pid timer) (armTimer pid timer delay jc) := by
  have peerRead (q : PeerId) : SameView (except pid timer) (getPeer q) := by
    intro s
    exact hoare_consequence (read_peer q (fun w => except pid timer w = s))
      (fun _ h => h) (fun _ _ h => h.1)

  have ambient {α : Type} (a : AmbientM α) : SameView (except pid timer) (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => except pid timer w = initial)
  have read : SameView (except pid timer) (get : WG.M WGWorld) := by
    intro initial
    exact hoare_consequence (hoare_get (fun w => except pid timer w = initial))
      (fun _ h => h) (fun _ _ h => h.2)
  have dev : SameView (except pid timer) getDev := by
    unfold getDev
    apply SameView.bind read
    intro w
    cases w.dev with
    | none => exact ambient (AmbientM.invariant _)
    | some d => exact SameView.pure _ d
  have stopped {α : Type} (e : Stop) : SameView (except pid timer) (throw e : WG.M α) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hr
    cases hr
  have edit (f : WGWorld → WGWorld) (hf : ∀ w, except pid timer (f w) = except pid timer w) :
      SameView (except pid timer) (modify f : WG.M Unit) := by
    intro initial
    apply hoare_modify
    intro w hw
    exact (hf w).trans hw
  unfold armTimer
  simp (config := { zeta := false }) only [getAmbient, hidden, invariant, unsupported]
  repeat' first
    | rxqueue_join_let
    | rxqueue_join_use
    | (snapshot_head placeOnWheel; exact placeOnWheel_except pid _ _ _ _)
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

theorem delTimer_except (pid : PeerId) (timer : PeerTimer) :
    SameView (except pid timer) (delTimer pid timer) := by
  intro initial
  unfold delTimer
  apply hoare_bind _ _ (read_peer pid (fun w => except pid timer w = initial))
  intro p
  apply write_peer pid timer p _ initial
  intro other different
  cases timer <;> cases other <;> first | contradiction | rfl

theorem armTimer_other (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64)
    (w v : WGWorld) (a b : Ambient)
    (run : ((armTimer pid timer delay caller).run w).run a = .ok (((),v),b))
    (q : PeerId) (t : PeerTimer) (other : ¬(q = pid ∧ t = timer)) :
    view v q t = view w q t := by
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp (armTimer_except pid timer delay caller)
    w a () v b run
  have point := congrFun (congrFun frame q) t
  simpa only [except,ite_eq_right other] using point

theorem delTimer_other (pid : PeerId) (timer : PeerTimer) (w v : WGWorld) (a b : Ambient)
    (run : ((delTimer pid timer).run w).run a = .ok (((),v),b))
    (q : PeerId) (t : PeerTimer) (other : ¬(q = pid ∧ t = timer)) :
    view v q t = view w q t := by
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp (delTimer_except pid timer)
    w a () v b run
  have point := congrFun (congrFun frame q) t
  simpa only [except,ite_eq_right other] using point

theorem delTimer_no_wheel (pid : PeerId) (timer : PeerTimer) (w v : WGWorld) (a b : Ambient)
    (run : ((delTimer pid timer).run w).run a = .ok (((),v),b)) :
    ∀ stamp expires entry, view v pid timer ≠ some (stamp,expires,some entry) := by
  unfold delTimer at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,read,write⟩ := run
  obtain ⟨rfl,rfl,d,hd,hp⟩ := Queues.getPeer_normal pid w u p a c read
  cases write
  intro stamp expires entry
  cases timer <;> simp [view,hd,Peer.setTimer,Peer.setWheel,Peer.timer,Peer.wheel]

end Leanux.Proofs.WG.AuthenticatedEffects.TimerSlots
