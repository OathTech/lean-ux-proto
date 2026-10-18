import Leanux.Proofs.WG.AuthenticatedEffects.CookieObservation

/-! Output-width properties of the executable crypto functions. These are
representation facts, not cryptographic security assumptions or claims. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG

private theorem bytes_words_length (ws : List UInt32) :
    ((pinned_const _private.Leanux.WG.NoiseCrypto.«0».Leanux.WG.bytesOfWords) ws).length =
      ws.length * 4 := by
  change (ws.flatMap fun w => (List.range 4).map fun k => (w >>> (8 * k).toUInt32).toUInt8).length = _
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_range, ih, List.length_cons]
    omega

theorem chacha_block_length (key : List UInt8) (counter : Nat) (nonce : List UInt8) :
    (chacha20Block key counter nonce).length = 64 := by
  unfold chacha20Block
  rw [bytes_words_length]
  simp

private theorem natLe_length (n len : Nat) :
    ((pinned_const _private.Leanux.WG.NoiseCrypto.«0».Leanux.WG.natLe) n len).length = len := by
  change ((List.range len).map fun i => (n / 256 ^ i % 256).toUInt8).length = len
  simp

theorem poly1305_length (key msg : List UInt8) : (poly1305 key msg).length = 16 := by
  exact natLe_length _ 16

theorem chacha_sixteen_length (key nonce plain : List UInt8) (counter : Nat)
    (length : plain.length = 16) : (chacha20 key counter nonce plain).length = 16 := by
  simp [chacha20, length, List.range_succ, chacha_block_length]

private theorem aeadTag_length (key nonce aad ciphertext : List UInt8) :
    ((pinned_const _private.Leanux.WG.NoiseCrypto.«0».Leanux.WG.aeadTag) key nonce aad ciphertext).length = 16 :=
  poly1305_length _ _

theorem xchacha_sixteen_length (key nonce plain aad : List UInt8)
    (length : plain.length = 16) : (xchachaEncrypt key nonce plain aad).length = 32 := by
  simp [xchachaEncrypt,aeadEncrypt,
    aeadTag_length, chacha_sixteen_length _ _ _ _ length]

private theorem compress_size (h : Array UInt32) (block : Array UInt8) (t : Nat) (last : Bool) :
    ((pinned_const _private.Leanux.WG.Blake2s.«0».Leanux.WG.compress) h block t last).size = 8 := by
  cases last
  all_goals run_tac Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkCIdent
    (Leanux.Proofs.Framing.normalizePinnedName `_private.Leanux.WG.Blake2s.«0».Leanux.WG.compress)):ident))
  all_goals simp

private theorem fold_array_size (f : Array UInt32 → Nat → Array UInt32)
    (hf : ∀ h i, (f h i).size = 8) (xs : List Nat) (h : Array UInt32)
    (hh : h.size = 8) : (xs.foldl f h).size = 8 := by
  induction xs generalizing h with
  | nil => exact hh
  | cons x xs ih => exact ih (f h x) (hf h x)

private theorem flat_words_length (ws : List UInt32) :
    (ws.flatMap fun w => (List.range 4).map fun k => (w >>> (8 * k).toUInt32).toUInt8).length =
      ws.length * 4 := bytes_words_length ws

theorem blake2s_sixteen_length (key data : List UInt8) : (blake2s 16 key data).length = 16 := by
  simp only [blake2s]
  change (((_ : Array UInt32).toList.flatMap fun w : UInt32 =>
    (List.range 4).map fun k => (w >>> (8 * k).toUInt32).toUInt8).take 16).length = 16
  rw [List.length_take,flat_words_length]
  simp only [Array.length_toList]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
  change min 16 ((List.foldl _ _ _ : Array UInt32).size * 4) = 16
  rw [fold_array_size _ (fun _ _ => compress_size _ _ _ _) _ _ (by rfl)]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects
