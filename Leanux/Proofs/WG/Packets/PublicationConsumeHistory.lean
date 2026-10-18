import Leanux.Proofs.WG.Packets.PublicationPrepareInvariant

/-! An actual consume freezes the same selected packet and uses its earlier
publication occurrence. Normal nondelivery is covered; only successful calls
emit a consume receipt, exactly as the existing observer specifies. -/
namespace Leanux.Proofs.WG.PublicationHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues PublicationIdentity
open Origins.HistorySupport (sessions)

/-- A normal consume, including None, carries its publication certificate
from a specified strict earlier decrypt occurrence. The enclosing
caller must supply this invariant on its own outer prefix; the nested journal
is arbitrary. No initialized runner reachability is asserted here. -/
theorem consume_anchored (history : List RxHistory.Event) (pid occurrence id : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) (w v : World)
    (h t : List RxJoint.Event) (value : Option RxJoint.Entry)
    (packets : Inv history w.wg) (selected : RxDisposition.SelectedAt id stamp pkt w)
    (peer : pkt.peer = pid) (crypted : pkt.state = .crypted)
    (hr : runPrefix (RxJoint.consume pid occurrence id stamp pkt ep) w h = (.ok (value,v),t)) :
    ∃ prior later, ∃ (decrypt : WGRunWitness (RxPacket × Option RxPacket)),
      ∃ out publishedPeer published publicationAmbient,
      ∃ (receipt : RxDisposition.ConsumeReceipt), ∃ before after,
      history = prior ++ .rx (.decrypt id decrypt) :: later ∧
      Published id decrypt out publishedPeer published publicationAmbient ∧
      receipt.run.before = w.wg ∧ receipt.run.ambientBefore = w.ambient ∧
      receipt.run.after = v.wg ∧ receipt.run.ambientAfter = v.ambient ∧
      ConsumeCertificate (sessions prior) id decrypt out publishedPeer published stamp receipt ∧
      t = h ++ before ++ [.consumed occurrence id stamp receipt] ++ after ∧
      ∀ e, value = some e → e.origin = some receipt ∧ receipt.run.value = some e.tag.bytes := by
  have erases := RxJoint.access_erases
    (liftWGObserver_erases (consumeDataDonePrefix_erases pid pkt ep)) w h
  obtain ⟨before,hbefore⟩ := RxJoint.access_appends
    (liftWGObserver (consumeDataDonePrefix pid pkt ep)) w h
  rw [RxJoint.consume_run] at hr
  cases run : runPrefix (RxJoint.access (liftWGObserver (consumeDataDonePrefix pid pkt ep))) w h with
  | mk result journal =>
    simp only [run] at hr erases hbefore
    cases result with
    | error stop => cases hr
    | ok result =>
      rcases result with ⟨returned,final⟩
      let receipt : RxDisposition.ConsumeReceipt :=
        ⟨pid,pkt,ep,⟨returned,w.wg,final.wg,w.ambient,final.ambient⟩⟩
      have valid : receipt.Valid := by
        change ((consumeDataDone pid pkt ep).run w.wg).run w.ambient =
          .ok ((returned,final.wg),final.ambient)
        have equation := erases.symm
        rw [liftWG_run] at equation
        cases native : ((consumeDataDone pid pkt ep).run w.wg).run w.ambient with
        | error stop => simp [native,Except.map] at equation
        | ok endpoint =>
          rcases endpoint with ⟨⟨x,g⟩,ambient⟩
          simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at equation
          obtain ⟨rfl,rfl⟩ := equation
          rfl
      have source : RxLink.Source id stamp receipt := ⟨valid,selected,peer⟩
      obtain ⟨prior,later,decrypt,out,publishedPeer,published,publicationAmbient,position,publication,certificate⟩ :=
        packets.receipt source crypted
      cases returned with
      | none =>
        cases hr
        refine ⟨prior,later,decrypt,out,publishedPeer,published,publicationAmbient,receipt,before,[],
          position,publication,rfl,rfl,rfl,rfl,certificate,?_,?_⟩
        · simp only [hbefore,List.append_nil]
          rfl
        · intro e impossible
          cases impossible
      | some bytes =>
        cases hr
        refine ⟨prior,later,decrypt,out,publishedPeer,published,publicationAmbient,receipt,before,
          [.buffered ⟨⟨occurrence,id,bytes⟩,stamp,some receipt⟩],
          position,publication,rfl,rfl,rfl,rfl,certificate,?_,?_⟩
        · simp only [hbefore]
          rfl
        · intro e same
          cases same
          exact ⟨rfl,rfl⟩

end Leanux.Proofs.WG.PublicationHistory
