import Leanux.Proofs.WG.TransmitSecurity.NonceStagingSafety

/-! Bounded native sending counters have distinct wire and AEAD nonces.
This is the representation link, separate from allocation-to-packet transport. -/
namespace Leanux.Proofs.WG.TransmitSecurity
open Leanux Leanux.WG

theorem le64_injective {n m : Nat} (hn : n < 2 ^ 64) (hm : m < 2 ^ 64)
    (same : le64 n = le64 m) : n = m := by
  have h0 := congrArg (fun bs : List UInt8 => (bs.getD 0 0).toNat) same
  have h1 := congrArg (fun bs : List UInt8 => (bs.getD 1 0).toNat) same
  have h2 := congrArg (fun bs : List UInt8 => (bs.getD 2 0).toNat) same
  have h3 := congrArg (fun bs : List UInt8 => (bs.getD 3 0).toNat) same
  have h4 := congrArg (fun bs : List UInt8 => (bs.getD 4 0).toNat) same
  have h5 := congrArg (fun bs : List UInt8 => (bs.getD 5 0).toNat) same
  have h6 := congrArg (fun bs : List UInt8 => (bs.getD 6 0).toNat) same
  have h7 := congrArg (fun bs : List UInt8 => (bs.getD 7 0).toNat) same
  simp [le64, List.range_succ] at h0 h1 h2 h3 h4 h5 h6 h7
  omega

theorem admitted_counter_bound {n : Nat} (hn : n < REJECT_AFTER_MESSAGES) : n < 2 ^ 64 := by
  simp only [REJECT_AFTER_MESSAGES, COUNTER_WINDOW_SIZE] at hn
  omega

theorem admitted_aead_nonce_injective {n m : Nat}
    (hn : n < REJECT_AFTER_MESSAGES) (hm : m < REJECT_AFTER_MESSAGES)
    (same : counterNonce n = counterNonce m) : n = m := by
  apply le64_injective (admitted_counter_bound hn) (admitted_counter_bound hm)
  exact List.append_cancel_left same

end Leanux.Proofs.WG.TransmitSecurity
