import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumeLeafPointArmJoin

import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProductReadFrames

/-! Canonical wheel source. The saved peer is the value of the original first
read; every write and every later check remains in its original position. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Wheel.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

abbrev History := List Event
abbrev Result (α : Type) := Except Stop (α × World)
abbrev wg (body : WG.M α) : PrefixM Event α := Consume.Leaf.wg body

def body (pid : PeerId) (t : PeerTimer) (expires clk : UInt64) (unit? : Option Nat) (p : Peer) : WG.M Unit := do
  match TimerWheel.place p t expires clk with
  | .kept _ =>
    setPeer pid (p.setTimer t (some expires))
    if unit?.isSome then
      if (← peekHiddenSite) == some HiddenSite.timerEnqueue.info.id then
        throw (.hidden s!"Linux re-enqueued peer {pid}'s {repr t} timer, which the mirror keeps in its slot (expires {expires}, base clock {clk})")
  | .enqueued slot bexp =>
    if let some u := unit? then
      let eb ← hidden .timerEnqueue
      let (ridx, rbexp, u3) := (recordWord eb 0, recordWord64 eb 1, recordWord eb 2)
      if u != 0 && u3 != u then
        throw (.hidden s!"the enqueue record names timer {u3}, the arm record {u}")
      if ridx != slot || rbexp != bexp then
        throw (.hidden s!"wheel arithmetic differs from Linux for peer {pid}'s {repr t} timer: expires {expires}, base clock {clk}: the mirror puts it in slot {slot} at bucket expiry {bexp}, Linux in slot {ridx} at {rbexp}")
    let lvl := TimerWheel.levelOf slot
    if !(timeAfter bexp expires && timeBeforeEq bexp (expires + (TimerWheel.LVL_GRAN lvl).toUInt64)) then
      invariant s!"a bucket expiry {bexp} outside (expires, expires + 8^{lvl}] for expires {expires}"
    let stamp := (← get).timerEnqueues + 1
    modify fun k => { k with timerEnqueues := stamp }
    setPeer pid ((p.setTimer t (some expires)).setWheel t (some ⟨slot, bexp, stamp⟩))
  if let some what := TimerWheel.peerWheelProblem (← getPeer pid) then
    invariant s!"peer {pid}'s timers: {what}"

theorem source_factor (pid : PeerId) (timer : PeerTimer) (expires clock : UInt64) (unit : Option Nat) :
    placeOnWheel pid timer expires clock unit = (getPeer pid >>= body pid timer expires clock unit) := rfl

noncomputable def readRemainder {w : World} {id : PeerId} (h : History)
    (point : ReadAccess.Point (ReadAccess.peerShape id) w.wg w.ambient v b) : PrefixM Event Peer :=
  ProductRead.remainder h (ProductRead.Point.wg point)

theorem readRemainder_run {w : World} {id : PeerId} (h : History)
    (point : ReadAccess.Point (ReadAccess.peerShape id) w.wg w.ambient v b) :
    runPrefix (wg (getPeer id)) w h=runPrefix (readRemainder h point) {w with wg:=v,ambient:=b} h := by
  change runPrefix (liftWGObserver (liftWGPrefix (getPeer id))) w h=_
  rw [liftWGObserver_lift]
  exact ProductRead.remainder_run h (.wg point)

inductive Native (pid : PeerId) (saved : Peer) where
  | ambient {α : Type} (action : AmbientM α)
  | world
  | peer (id : PeerId)
  | stamp (value : Nat)
  | install (peer : Peer)
      (same : peer.internalId = saved.internalId ∧ peer.staged = saved.staged ∧ peer.txQueue = saved.txQueue)
  | failure {α : Type} (reason : Stop)

def Native.Result : Native pid saved → Type
  | @Native.ambient _ _ α _ => α
  | .world => WGWorld
  | .peer _ => Peer
  | .stamp _ | .install .. => Unit
  | @Native.failure _ _ α _ => α

def Native.body (token : Native pid saved) : WG.M token.Result := match token with
  | .ambient action => monadLift action
  | .world => get
  | .peer id => getPeer id
  | .stamp value => modify fun w => {w with timerEnqueues := value}
  | .install occupant _ => setPeer pid occupant
  | .failure reason => throw reason

abbrev Native.action (token : Native pid saved) : PrefixM Event token.Result := wg token.body

inductive Shape (pid : PeerId) (saved : Peer) : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape pid saved (pure value)
  | native (token : Native pid saved) : Shape pid saved token.action
  | failed {α β : Type} {action : PrefixM Event α} (failure : Consume.Leaf.Failure action)
      (next : α → PrefixM Event β) : Shape pid saved (action >>= next)
  | bind {action : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape pid saved action) (tail : ∀ value, Shape pid saved (next value)) : Shape pid saved (action >>= next)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Wheel.Points
