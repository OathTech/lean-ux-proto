import Leanux.Proofs.WG.HandshakeSecurity.ResponderHistoryFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.History
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

theorem consume (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges)
    (base : List Nat) (pid occurrence id : Nat) (stamp : PacketStamp)
    (pkt : RxPacket) (ep : Endpoint) :
    PrefixPreserves (State base) (Checks base) (RxJoint.consume pid occurrence id stamp pkt ep) := by
  intro w h hi
  have erases := RxJoint.access_erases
    (liftWGObserver_erases (consumeDataDonePrefix_erases pid pkt ep)) w h
  obtain ⟨s, appends⟩ := RxJoint.access_appends
    (liftWGObserver (consumeDataDonePrefix pid pkt ep)) w h
  have frame := focusPrefix_other RxJoint.Event.access RxJoint.accessEvent consumer
    (fun _ => rfl) (liftWGObserver (consumeDataDonePrefix pid pkt ep)) w h
  change (runPrefix (RxJoint.access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h).2.filterMap consumer = h.filterMap consumer at frame
  have empty : s.filterMap consumer = [] := by
    rw [appends, List.filterMap_append] at frame
    simpa using frame
  have safe : Checks base (runPrefix (RxJoint.access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h).2 :=
    appends ▸ hi.2.quiet empty
  have labelFrame : labels (runPrefix (RxJoint.access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h).2 = labels h := by
    rw [labels_consumer, labels_consumer, frame]
  rw [RxJoint.consume_run]
  cases run : runPrefix (RxJoint.access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk result t =>
    simp only [run] at erases appends safe labelFrame
    cases result with
    | error stop => exact ⟨s, appends, safe, True.intro⟩
    | ok result =>
      rcases result with ⟨returned, v⟩
      let r : RxDisposition.ConsumeReceipt := ⟨pid, pkt, ep,
        ⟨returned, w.wg, v.wg, w.ambient, v.ambient⟩⟩
      have valid : r.Valid := by
        change ((consumeDataDone pid pkt ep).run w.wg).run w.ambient =
          .ok ((returned, v.wg), v.ambient)
        have equation := erases.symm
        rw [liftWG_run] at equation
        cases native : ((consumeDataDone pid pkt ep).run w.wg).run w.ambient with
        | error stop => simp [native, Except.map] at equation
        | ok endpoint =>
          rcases endpoint with ⟨⟨x, g⟩, ambient⟩
          simp only [native, Except.map, Except.ok.injEq, Prod.mk.injEq] at equation
          obtain ⟨rfl, rfl⟩ := equation
          rfl
      have auth := completed_consumer_history H1 slots (base ++ labels h) r valid hi.1.1
      have bounds := (hoare_iff_run_ambient _ _ _).mp
        (CurrentSlots.consumeDataDone_preserves pid pkt ep) w.wg w.ambient returned v.wg v.ambient hi.1.2 valid
      have checked : Checks base (t ++ [.consumed occurrence id stamp r]) :=
        safe.snoc (by change Native (base ++ labels t) w.wg; rw [labelFrame]; exact hi.1)
      have post : Native (base ++ labels (t ++ [.consumed occurrence id stamp r])) v.wg := by
        rw [labels_append, labels_consumed, labelFrame, ← List.append_assoc]
        exact ⟨auth, bounds⟩
      cases returned with
      | none =>
        exact ⟨s ++ [.consumed occurrence id stamp r],
          by simp only [appends, List.append_assoc]; rfl, checked, post, checked⟩
      | some bytes =>
        let entry : RxJoint.Entry := ⟨⟨occurrence, id, bytes⟩, stamp, some r⟩
        have buffered := checked.snoc (e := .buffered entry) True.intro
        refine ⟨s ++ [_, _], by simp only [appends, List.append_assoc]; rfl, buffered, ?_, buffered⟩
        change Native (base ++ labels ((t ++ [.consumed occurrence id stamp r]) ++ [.buffered entry])) v.wg
        rw [labels_append, labels_buffered, List.append_nil]
        exact post

end Leanux.Proofs.WG.HandshakeSecurity.Responder.History
