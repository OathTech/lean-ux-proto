import Leanux.Proofs.WG.Noise.ResponseCallerFinalFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ResponseCaller
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- The actual final tags equal those at the last completed receipt. Shape
separately guarantees a creator receipt and a session receipt iff created. -/
def ReceiptFinalTags (receipts : List TagReceipt) (final : Campaign2.Snapshot) : Prop :=
  ∃ last, receipts.getLast? = some last ∧ final.tagAt = last.after.tagAt

theorem observeProjected_finalTags (pid : PeerId) :
    Campaign2.Ensures (observeProjected pid) (fun _ => True)
      (fun receipts final => ReceiptFinalTags receipts final) := by
  intro g ambient receipts final after pre run
  change (((observeNative pid).run g).run ambient >>= fun ((history, current), inputs) =>
    Except.ok ((history.map Event.receipt, current), inputs)) = _ at run
  cases actual : ((observeNative pid).run g).run ambient with
  | error stop => rw [actual] at run; cases run
  | ok out =>
    obtain ⟨⟨history, current⟩, inputs⟩ := out
    rw [actual] at run
    cases run
    have framed := observeNative_lastTags pid g ambient history final after pre actual
    have shape := (observeNative_claim pid g ambient history final after pre actual).1
    rcases shape with ⟨created, rfl, empty⟩ | ⟨created, session, rfl, present⟩
    · exact ⟨(Event.created pid created).receipt, rfl, framed _ rfl⟩
    · exact ⟨(Event.session pid session).receipt, rfl, framed _ rfl⟩

/-- Whole original-response tag linkage: the entry reaches the creator,
creator output reaches session input, and the last actual receipt reaches
the final state. All intermediate helper frames are instantiated here. -/
theorem original_response_receipt_final_tags (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observeProjected pid) (fun s => s.tagAt = entry.tagAt)
      (fun receipts final => ReceiptShape pid receipts ∧ ReceiptChain entry receipts ∧
        ReceiptRoles pid entry receipts ∧ ReceiptFinalTags receipts final ∧
        ∀ receipt ∈ receipts, ReceiptValid receipt ∧ TagReceiptEffect receipt) := by
  intro g ambient receipts final after pre run
  have linked := original_response_receipt_chain pid entry
    g ambient receipts final after pre run
  have ending := observeProjected_finalTags pid
    g ambient receipts final after True.intro run
  exact ⟨linked.1, linked.2.1, linked.2.2.1, ending, linked.2.2.2⟩

end Leanux.Proofs.WG.Noise.ResponseCaller
