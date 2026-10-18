import Leanux.Proofs.WG.TransmitSecurity.EncryptSource

/-! Every original successful encryption has one receipt for its actual native
preparation and key read. Failure before the AEAD produces no such receipt. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Encryption
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem observe_run (checksum : Packet → Leanux.M Packet) (slot : KeypairId) (pkt : DataPacket)
    (w : World) (h : List Receipt) :
    runPrefix (observe checksum slot pkt) w h =
      match (prepare checksum pkt).run w with
      | .error stop => (.error stop,h)
      | .ok (none,u) => (.ok (none,u),h)
      | .ok (some p,u) =>
        match (liftWG (getKeypair slot)).run u with
        | .error stop => (.error stop,h)
        | .ok (k,v) =>
          match (branch .encSgvecFailed false : Leanux.M Bool).run v with
          | .error stop => (.error stop,h)
          | .ok (failed,z) =>
            if failed then (.ok (none,z),h)
            else
              let r : Receipt := ⟨slot,pkt,p,⟨some p,w,u⟩,⟨k,u,v⟩⟩
              (.ok (some r.ciphertext,z),h ++ [r]) := by
  unfold observe
  rw [runPrefix_bind,runPrefix_captureRun]
  cases preparation : (prepare checksum pkt).run w with
  | error stop => rfl
  | ok out =>
    rcases out with ⟨prepared,u⟩
    cases prepared with
    | none => rfl
    | some p =>
      simp only [runPrefix_bind,runPrefix_captureRun]
      cases keyRead : (liftWG (getKeypair slot)).run u with
      | error stop => rfl
      | ok out =>
        rcases out with ⟨k,v⟩
        simp only [runPrefix_lift]
        cases checked : (branch .encSgvecFailed false : Leanux.M Bool).run v with
        | error stop => rfl
        | ok out =>
          rcases out with ⟨failed,z⟩
          cases failed <;> rfl

theorem observe_receipts (checksum : Packet → Leanux.M Packet) (slot : KeypairId) (pkt : DataPacket)
    (w : World) (h : List Receipt) :
    ∃ suffix, (runPrefix (observe checksum slot pkt) w h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix,
        r.slot = slot ∧ r.packet = pkt ∧ r.Valid checksum := by
  rw [observe_run]
  cases preparation : (prepare checksum pkt).run w with
  | error stop => exact ⟨[],by simp⟩
  | ok out =>
    rcases out with ⟨prepared,u⟩
    cases prepared with
    | none => exact ⟨[],by simp⟩
    | some p =>
      cases keyRead : (liftWG (getKeypair slot)).run u with
      | error stop => exact ⟨[],by simp [keyRead]⟩
      | ok out =>
        rcases out with ⟨k,v⟩
        simp only [keyRead]
        cases checked : (branch .encSgvecFailed false : Leanux.M Bool).run v with
        | error stop => exact ⟨[],by simp⟩
        | ok out =>
          rcases out with ⟨failed,z⟩
          cases failed with
          | true => exact ⟨[],by simp⟩
          | false =>
            refine ⟨[⟨slot,pkt,p,⟨some p,w,u⟩,⟨k,u,v⟩⟩],rfl,by simp,?_⟩
            intro r member
            have same := List.mem_singleton.mp member
            subst r
            exact ⟨rfl,rfl,preparation,rfl,rfl,keyRead⟩

theorem original_success_receipt (checksum : Packet → Leanux.M Packet)
    (slot : KeypairId) (pkt : DataPacket) (w v : World) (bytes : List UInt8)
    (h : List Receipt)
    (success : (encryptPacket checksum slot pkt).run w = .ok (some bytes,v)) :
    ∃ r, runPrefix (observe checksum slot pkt) w h = (.ok (some bytes,v),h ++ [r]) ∧
      r.slot = slot ∧ r.packet = pkt ∧ r.Valid checksum ∧
      r.preparation.before = w ∧ r.ciphertext = bytes := by
  have erased := observe_erases checksum slot pkt w h
  rw [success] at erased
  rw [observe_run] at erased ⊢
  cases preparation : (prepare checksum pkt).run w with
  | error stop => simp [preparation] at erased
  | ok out =>
    rcases out with ⟨prepared,u⟩
    cases prepared with
    | none => simp [preparation] at erased
    | some p =>
      cases keyRead : (liftWG (getKeypair slot)).run u with
      | error stop => simp [preparation,keyRead] at erased
      | ok out =>
        rcases out with ⟨k,z⟩
        cases checked : (branch .encSgvecFailed false : Leanux.M Bool).run z with
        | error stop => simp [preparation,keyRead,checked] at erased
        | ok out =>
          rcases out with ⟨failed,last⟩
          cases failed with
          | true => simp [preparation,keyRead,checked] at erased
          | false =>
            simp only [preparation,keyRead,checked,Bool.false_eq_true,↓reduceIte,
              Except.ok.injEq,Prod.mk.injEq,Option.some.injEq] at erased
            obtain ⟨same,rfl⟩ := erased
            refine ⟨⟨slot,pkt,p,⟨some p,w,u⟩,⟨k,u,z⟩⟩,?_,rfl,rfl,⟨preparation,rfl,rfl,keyRead⟩,rfl,same⟩
            simp only [keyRead,checked,Bool.false_eq_true,↓reduceIte,same]

end Leanux.Proofs.WG.TransmitSecurity.Encryption
