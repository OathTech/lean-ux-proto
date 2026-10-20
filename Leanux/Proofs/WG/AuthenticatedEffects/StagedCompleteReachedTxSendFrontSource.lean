import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxSocketWorker

/-! Peer-read and family-guard cuts of the actual send callback, including
the unsupported-family path before its outer receipt. No cut assumes ownership. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSendFront
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompletionFirstTerminal
abbrev History := List CausalJournal.Event

structure ReadEntry (pid : PeerId) (w : World) (h : History) where
  peer : RunWitness Peer
  world : World
  events : List Completion.Event
  read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w
    (h.filterMap CausalJournal.completion?)=(.ok (peer,world),h.filterMap CausalJournal.completion?++events)

def ReadEntry.history (entry : ReadEntry pid w h) : History := h++entry.events.map FirstTerminal.encode

def afterFourNo (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) (peer : RunWitness Peer) :
    PrefixM Completion.Event Bool := do
  let ret ← if ← liftPrefix (liftWG (branch .sendSkbInet6 ((peer.value.endpoint.map (·.family)).getD 0 == AF_INET6))) then
    Completion.socket pid skb packet peer false else pure (-EAFNOSUPPORT)
  afterSocket pid packet ret

inductive Stage where
  | read | fourNo | selected (ipv4 : Bool) | unsupported | refused

def Stage.Allowed (stage : Stage) (peer : RunWitness Peer) : Prop := match stage with
  | .read=>True
  | .fourNo=>(peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET
  | .selected ipv4=>SelectedFamily ipv4 peer
  | .unsupported | .refused=>
      (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET ∧ (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET6

def Stage.world (stage : Stage) (w : World) : World := match stage with
  | .read=>w
  | .fourNo=>{w with ambient:=CounterWindow.record w.ambient .sendSkbInet false}
  | .selected ipv4=>familyWorld ipv4 w
  | .unsupported=>{w with ambient:=CounterWindow.record (CounterWindow.record w.ambient .sendSkbInet false) .sendSkbInet6 false}
  | .refused=>refusedWorld w

def Stage.body (stage : Stage) (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) (peer : RunWitness Peer) :
    PrefixM Completion.Event Bool := match stage with
  | .read=>afterPeer pid skb packet peer
  | .fourNo=>afterFourNo pid skb packet peer
  | .selected ipv4=>Completion.socket pid skb packet peer ipv4 >>= afterSocket pid packet
  | .unsupported=>afterSocket pid packet (-EAFNOSUPPORT)
  | .refused=>pure false

private theorem branch_run (w : World) (decision : Decision) (value : Bool) :
    (liftWG (branch decision value)).run w=
      .ok (value,{w with ambient:=CounterWindow.record w.ambient decision value}) := rfl

theorem Stage.run (stage : Stage) (allowed : stage.Allowed peer) :
    runPrefix (afterPeer pid skb packet peer) w h=runPrefix (stage.body pid skb packet peer) (stage.world w) h := by
  cases stage with
  | read=>rfl
  | fourNo=>
      simp only [Stage.body,Stage.world,afterPeer,afterFourNo,beq_eq_false_iff_ne.mpr allowed,
        runPrefix_bind,runPrefix_lift,branch_run,Bool.false_eq_true,ite_false]
  | selected ipv4=>
      cases ipv4 with
      | false=>exact CompletionSendCuts.afterPeer6_run pid skb packet peer w h allowed.1 allowed.2
      | true=>exact CompletionSendCuts.afterPeer4_run pid skb packet peer w h allowed
  | unsupported=>
      simp only [Stage.body,Stage.world,afterPeer,beq_eq_false_iff_ne.mpr allowed.1,
        beq_eq_false_iff_ne.mpr allowed.2,runPrefix_bind,runPrefix_lift,branch_run,Bool.false_eq_true,ite_false,runPrefix_pure]
  | refused=>exact CompletionFirstTerminal.unsupported pid skb packet peer w h allowed.1 allowed.2

theorem Stage.focused_run (stage : Stage) (allowed : stage.Allowed peer) :
    runPrefix (FirstTerminal.focused (afterPeer pid skb packet peer)) w h=
      runPrefix (FirstTerminal.focused (stage.body pid skb packet peer)) (stage.world w) h := by
  change ((runPrefix (afterPeer pid skb packet peer) w _).1,h++List.map FirstTerminal.encode _)=_
  rw [stage.run allowed]
  rfl

theorem outer_run_equal {left right : PrefixM CausalJournal.Event Bool}
    (same : runPrefix left w h=runPrefix right u middle) :
    runPrefix (TxSocket.outer pid skb packet origin left) w h=
      runPrefix (TxSocket.outer pid skb packet origin right) u middle := by
  change (match runPrefix left w h with
    | (.error stop,last)=>(Except.error (α:=Bool×World) stop,last)
    | (.ok (value,v),last)=>(.ok (value,v),last++[CausalJournal.Event.sendResult ⟨pid,skb,packet,⟨value,origin,v⟩⟩]))=_
  rw [same]
  rfl

def ReadEntry.remaining (entry : ReadEntry pid w h) (skb : SkbId) (packet : RunWitness DataPacket) (stage : Stage) :
    PrefixM CausalJournal.Event Bool :=
  TxSocket.outer pid skb packet w (FirstTerminal.focused (stage.body pid skb packet entry.peer))

theorem ReadEntry.continuation (entry : ReadEntry pid w h) (stage : Stage) (allowed : stage.Allowed entry.peer) :
    runPrefix (CausalJournal.completionOps.send pid skb packet) w h=
      runPrefix (entry.remaining skb packet stage) (stage.world entry.world) entry.history := by
  rw [TxSocket.outer_source]
  apply outer_run_equal
  exact (CompletionSendCuts.focused_after_read pid skb packet entry.peer w entry.world h entry.events entry.read).trans
    (stage.focused_run allowed)

inductive Point (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) (w : World) (h : History) :
    World → History → Prop where
  | guarded (entry : ReadEntry pid w h) (stage : Stage) (allowed : stage.Allowed entry.peer) :
      Point pid skb packet w h (stage.world entry.world) entry.history
  | returned (performed : runPrefix (CausalJournal.completionOps.send pid skb packet) w h=(.ok (sent,u),middle)) :
      Point pid skb packet w h u middle

theorem Point.remaining (point : Point pid skb packet w h u middle) :
    ∃remaining,runPrefix (CausalJournal.completionOps.send pid skb packet) w h=runPrefix remaining u middle := by
  cases point with
  | guarded entry stage allowed=>exact ⟨_,entry.continuation stage allowed⟩
  | returned performed=>exact ⟨pure _,performed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSendFront
