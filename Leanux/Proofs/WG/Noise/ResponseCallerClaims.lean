import Leanux.Proofs.WG.Noise.ResponseCallerSource

/-! Actual whole-response receipts projected through the campaign snapshot.
Normal receipt order and local edges do not assert tag framing between cuts. -/
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ResponseCaller
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- Normal whole-call receipt shape and checked helper effects, with no
caller-frame premise and no claim about tag changes between these cuts. -/
theorem original_response_receipts (pid : PeerId) :
    Campaign2.Ensures (observeProjected pid) (fun _ => True)
      (fun receipts _ => ReceiptShape pid receipts ∧
        ∀ receipt ∈ receipts, ReceiptValid receipt ∧ TagReceiptEffect receipt) := by
  intro g ambient receipts final after pre run
  change (((observeNative pid).run g).run ambient >>= fun ((history, current), inputs) =>
    Except.ok ((history.map Event.receipt, current), inputs)) = _ at run
  cases actual : ((observeNative pid).run g).run ambient with
  | error stop => rw [actual] at run; cases run
  | ok out =>
    obtain ⟨⟨history, current⟩, inputs⟩ := out
    rw [actual] at run
    cases run
    have checked := observeNative_claim pid g ambient history final after pre actual
    refine ⟨checked.1.project, ?_⟩
    intro receipt member
    obtain ⟨event, contained, rfl⟩ := List.mem_map.mp member
    have valid := (checked.2 event contained).1
    exact ⟨⟨event, rfl, valid⟩, Event.receipt_effect valid⟩

/-- Erasure through the Campaign2 observation interface includes every Stop
and every projected successful state. -/
theorem original_response_receipts_erases (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True)
      (do let _ ← observeProjected pid; pure ())
      (sendHandshakeResponse pid) := by
  rw [observeProjected_discard]
  intro g ambient pre
  rfl

/-- Only tags are linked across helper cuts. The timestamp and MAC fields can
change; this does not assert equality of the entire snapshots. -/
def ReceiptChain (entry : Campaign2.Snapshot) (receipts : List TagReceipt) : Prop :=
  (∃ created, receipts = [created] ∧ created.before.tagAt = entry.tagAt) ∨
  (∃ created session, receipts = [created, session] ∧
    created.before.tagAt = entry.tagAt ∧ session.before.tagAt = created.after.tagAt)

theorem NativeChain.project {entry : Campaign2.Snapshot} {history : List Event}
    (linked : NativeChain entry.tagAt history) :
    ReceiptChain entry (history.map Event.receipt) := by
  rcases linked with ⟨pid, created, rfl, before⟩ |
    ⟨pid, created, session, rfl, before, between⟩
  · exact Or.inl ⟨(Event.created pid created).receipt, rfl, before⟩
  · exact Or.inr ⟨(Event.created pid created).receipt, (Event.session pid session).receipt,
      rfl, before, between⟩

theorem observeProjected_chain (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observeProjected pid) (fun s => s.tagAt = entry.tagAt)
      (fun receipts _ => ReceiptChain entry receipts) := by
  intro g ambient receipts final after pre run
  change (((observeNative pid).run g).run ambient >>= fun ((history, current), inputs) =>
    Except.ok ((history.map Event.receipt, current), inputs)) = _ at run
  cases actual : ((observeNative pid).run g).run ambient with
  | error stop => rw [actual] at run; cases run
  | ok out =>
    obtain ⟨⟨history, current⟩, inputs⟩ := out
    rw [actual] at run
    cases run
    exact (observeNative_chain pid entry.tagAt g ambient history final after pre actual).project

/-- If the caller reaches the session receipt, its successful creator started
from consumed initiation at call entry and the actual session sees created
response. This also covers a session that returns false. -/
def ReceiptRoles (pid : PeerId) (entry : Campaign2.Snapshot) (receipts : List TagReceipt) : Prop :=
  ∀ created session, receipts = [created, session] →
    entry.tagAt pid = some HANDSHAKE_CONSUMED_INITIATION ∧
    session.before.tagAt pid = some HANDSHAKE_CREATED_RESPONSE

theorem receipt_roles {pid : PeerId} {entry : Campaign2.Snapshot} {receipts : List TagReceipt}
    (shape : ReceiptShape pid receipts) (linked : ReceiptChain entry receipts)
    (effects : ∀ receipt ∈ receipts, TagReceiptEffect receipt) :
    ReceiptRoles pid entry receipts := by
  intro created session pair
  subst receipts
  rcases shape with ⟨only, impossible, rest⟩ |
    ⟨c, s, msg, ok, same, createOp, createValue, sessionOp, sessionValue⟩
  · cases impossible
  · have equal := List.cons.inj same
    have equalTail := List.cons.inj equal.2
    have hc : c = created := equal.1.symm
    have hs : s = session := equalTail.1.symm
    subst c
    subst s
    rcases linked with ⟨only, impossible, rest⟩ |
      ⟨c, s, same, before, between⟩
    · cases impossible
    · have equal := List.cons.inj same
      have equalTail := List.cons.inj equal.2
      have hc : c = created := equal.1.symm
      have hs : s = session := equalTail.1.symm
      subst c
      subst s
      have effect := effects created (by simp only [List.mem_cons, true_or])
      simp only [TagReceiptEffect, createOp, createValue, Option.isSome_some, ite_true] at effect
      constructor
      · rw [← before]
        exact effect.2 True.intro
      · rw [between]
        simpa only [ite_true] using effect.1 pid

/-- Normal original-response observer, with actual receipt effects and derived
tag provenance through the initial timestamp and intervening MAC updates.
This is a prefix linkage claim; it imposes no post-session tag frame. -/
theorem original_response_receipt_chain (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observeProjected pid) (fun s => s.tagAt = entry.tagAt)
      (fun receipts _ => ReceiptShape pid receipts ∧ ReceiptChain entry receipts ∧
        ReceiptRoles pid entry receipts ∧
        ∀ receipt ∈ receipts, ReceiptValid receipt ∧ TagReceiptEffect receipt) := by
  intro g ambient receipts final after pre run
  have facts := original_response_receipts pid g ambient receipts final after True.intro run
  have linked := observeProjected_chain pid entry g ambient receipts final after pre run
  exact ⟨facts.1, linked, receipt_roles facts.1 linked (fun r hr => (facts.2 r hr).2), facts.2⟩

end Leanux.Proofs.WG.Noise.ResponseCaller
