import Leanux.Proofs.WG.Noise.PendingConsumeCoreFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues

def jointLabels (h : List RxJoint.Event) : List Nat :=
  CounterConsume.confirmationLabels (h.map RxHistory.promote)

def JointInv (seen : List Nat) (h : List RxJoint.Event) (w : World) : Prop :=
  NativeInv w.wg ((jointLabels h).reverse ++ seen)

def JointSafe (seen : List Nat) (h : List RxJoint.Event) : Prop :=
  ((jointLabels h).reverse ++ seen).Nodup

theorem access_labels {α : Type} (a : PrefixM LifetimeEvent α) (w : World) (h : List RxJoint.Event) :
    jointLabels (runPrefix (RxJoint.access a) w h).2 = jointLabels h := by
  unfold jointLabels CounterConsume.confirmationLabels
  simp only [List.filterMap_map]
  exact focusPrefix_other RxJoint.Event.access RxJoint.accessEvent
    (fun e => CounterConsume.eventLabel (RxHistory.promote e)) (fun _ => rfl) a w h

theorem jointLabels_append (h t : List RxJoint.Event) :
    jointLabels (h ++ t) = jointLabels h ++ jointLabels t := by
  simp only [jointLabels,List.map_append,CounterConsume.confirmationLabels,List.filterMap_append]

theorem consumed_seen (seen : List Nat) (h : List RxJoint.Event)
    (n id : Nat) (stamp : PacketStamp) (r : RxDisposition.ConsumeReceipt) :
    (jointLabels (h ++ [.consumed n id stamp r])).reverse ++ seen =
      PendingTickets.record (CounterConsume.receiptLabel r) ((jointLabels h).reverse ++ seen) := by
  rw [jointLabels_append,List.reverse_append]
  cases label : CounterConsume.receiptLabel r <;>
    simp [jointLabels,CounterConsume.confirmationLabels,RxHistory.promote,
      CounterConsume.eventLabel,PendingTickets.record,label]

theorem buffered_labels (h : List RxJoint.Event) (e : RxJoint.Entry) :
    jointLabels (h ++ [.buffered e]) = jointLabels h := by
  simp [jointLabels,CounterConsume.confirmationLabels,RxHistory.promote,
    CounterConsume.eventLabel]

private theorem native_of_lift {α : Type} (action : WG.M α)
    (w v : World) (value : α) (run : (liftWG action).run w = .ok (value,v)) :
    (action.run w.wg).run w.ambient = .ok ((value,v.wg),v.ambient) := by
  rw [liftWG_run] at run
  cases native : (action.run w.wg).run w.ambient with
  | error e => simp [native,Except.map] at run
  | ok out =>
    rcases out with ⟨⟨result,g⟩,ambient⟩
    simp [native,Except.map] at run
    obtain ⟨rfl,rfl⟩ := run
    rfl

/-- The actual local GRO journal adds precisely its same-run optional ticket.
Prior confirmations are retained explicitly even though the poll's seed contains
only lifetime events. Access failures append no confirmation ticket. -/
theorem consume (seen : List Nat) (pid n id : Nat) (stamp : PacketStamp)
    (pkt : RxPacket) (endpoint : Endpoint) :
    PrefixPreserves (JointInv seen) (JointSafe seen)
      (RxJoint.consume pid n id stamp pkt endpoint) := by
  intro w h hi
  have appended : ∃ suffix,
      (runPrefix (RxJoint.access (liftWGObserver (consumeDataDonePrefix pid pkt endpoint))) w h).2 =
        h ++ suffix := ⟨_,rfl⟩
  obtain ⟨suffix,append⟩ := appended
  have labels := access_labels (liftWGObserver (consumeDataDonePrefix pid pkt endpoint)) w h
  have erased := RxJoint.access_erases
    (liftWGObserver_erases (consumeDataDonePrefix_erases pid pkt endpoint)) w h
  rw [RxJoint.consume_run]
  cases run : runPrefix (RxJoint.access
      (liftWGObserver (consumeDataDonePrefix pid pkt endpoint))) w h with
  | mk result t =>
    simp only [run] at append labels erased
    cases result with
    | error stop =>
      refine ⟨suffix,append,?_,True.intro⟩
      change ((jointLabels t).reverse ++ seen).Nodup
      rw [labels]
      exact hi.2.2.distinct
    | ok out =>
      obtain ⟨returned,v⟩ := out
      let r : RxDisposition.ConsumeReceipt :=
        ⟨pid,pkt,endpoint,⟨returned,w.wg,v.wg,w.ambient,v.ambient⟩⟩
      have actual := native_of_lift (consumeDataDone pid pkt endpoint) w v returned erased.symm
      have core := consume_core pid pkt endpoint w.wg w.ambient returned v.wg v.ambient
        ⟨hi.1,hi.2.1⟩ actual
      have pending := (ConsumeConfirmation.receipt_optional_step r actual).preserves hi.2.2
      have settled : JointInv seen (t ++ [.consumed n id stamp r]) v := by
        change NativeInv v.wg ((jointLabels (t ++ [.consumed n id stamp r])).reverse ++ seen)
        rw [consumed_seen,labels]
        exact ⟨core.1,core.2,pending⟩
      cases returned with
      | none =>
        exact ⟨suffix ++ [_],by simp only [append,List.append_assoc]; rfl,
          settled.2.2.distinct,settled⟩
      | some bytes =>
        let e : RxJoint.Entry := ⟨⟨n,id,bytes⟩,stamp,some r⟩
        have final : JointInv seen ((t ++ [.consumed n id stamp r]) ++ [.buffered e]) v := by
          change NativeInv v.wg ((jointLabels _).reverse ++ seen)
          rw [buffered_labels]
          exact settled
        exact ⟨suffix ++ [_,_],by simp only [append,List.append_assoc]; rfl,
          final.2.2.distinct,final⟩

end Leanux.Proofs.WG.Noise.PendingSession
