import Leanux.Proofs.WG.Noise.DriverTagModel

/-! The driver tag coverage relation preserves the five named handshake states.
This is a consequence of the recorded owner effects, not a replacement for
those effects or for source receipt validity. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

def HandshakeTag (tag : Nat) : Prop :=
  tag = HANDSHAKE_ZEROED ∨ tag = HANDSHAKE_CREATED_INITIATION ∨
  tag = HANDSHAKE_CONSUMED_INITIATION ∨ tag = HANDSHAKE_CREATED_RESPONSE ∨
  tag = HANDSHAKE_CONSUMED_RESPONSE

def HandshakeTags (tags : TagMap) : Prop :=
  ∀ pid tag, tags pid = some tag → HandshakeTag tag

theorem HandshakeTags.retained {before after : TagMap}
    (valid : HandshakeTags before) (retained : TagsRetained before after) :
    HandshakeTags after :=
  fun pid tag present => valid pid tag (retained pid tag present)

theorem TagReceiptEffect.handshakeTags {receipt : TagReceipt}
    (effect : TagReceiptEffect receipt) (before : HandshakeTags receipt.before.tagAt) :
    HandshakeTags receipt.after.tagAt := by
  obtain ⟨operation,entry,result,final⟩ := receipt
  cases operation <;> cases result <;>
    simp only [TagReceiptEffect] at effect
  all_goals try contradiction
  all_goals
    intro pid tag present
    simp only [Campaign2.Snapshot.tagAt] at *
  all_goals
    first
    | have mapped := effect pid
      rw [mapped] at present
    | have mapped := effect.1 pid
      rw [mapped] at present
  all_goals
    repeat' split at present
    all_goals
      first
      | exact before pid tag present
      | (cases present; simp [HandshakeTag])

theorem PeerCreateEffect.handshakeTags {receipt : PeerCreateReceipt}
    (effect : PeerCreateEffect receipt) (before : HandshakeTags receipt.before.tagAt) :
    HandshakeTags receipt.after.tagAt := by
  intro pid tag present
  rw [effect.2 pid] at present
  cases result : receipt.result
  · simp only [result] at present
    exact before pid tag present
  · simp only [result] at present
    split at present
    · cases present; simp [HandshakeTag]
    · exact before pid tag present

theorem DriverTagEvent.Effect.handshakeTags {event : DriverTagEvent}
    (effect : event.Effect) (before : HandshakeTags event.before.tagAt) :
    HandshakeTags event.after.tagAt := by
  cases event with
  | helper receipt => exact TagReceiptEffect.handshakeTags effect before
  | peerCreate receipt => exact PeerCreateEffect.handshakeTags effect before

theorem DriverTagMapCoverage.handshakeTags {entry final : TagMap}
    {events : List DriverTagEvent} (coverage : DriverTagMapCoverage entry events final)
    (before : HandshakeTags entry) : HandshakeTags final := by
  induction events generalizing entry with
  | nil => exact before.retained coverage
  | cons event rest ih =>
    exact ih coverage.2.2 (coverage.2.1.handshakeTags (before.retained coverage.1))

theorem DriverTagMapCoverage.initialized_handshakeTags {final : TagMap}
    {events : List DriverTagEvent}
    (coverage : DriverTagMapCoverage (fun _ => none) events final) :
    HandshakeTags final :=
  coverage.handshakeTags (by intro pid tag present; cases present)

end Leanux.Proofs.WG.Noise
