import Leanux.Proofs.WG.Roaming.Basic
import Leanux.Proofs.WG.Noise.ConsumeEdges
import Leanux.WG.RxData

set_option autoImplicit false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Decryption itself preserves the outer source and packet ownership,
and successful plaintext is precisely the AEAD result under the receiving
key read from the specified resident keypair. No source-address binding is
asserted: the actual call has empty associated data. -/
theorem decryptPacket_authenticated (pkt : RxPacket) (key : Keypair) :
    Ensures (decryptPacket pkt)
      (fun g => (g.dev.bind fun d => d.keypairs[pkt.keypair]?) = some key)
      (fun result _ => ∀ plain, result = some plain →
        plain.source = pkt.source ∧ plain.peer = pkt.peer ∧ plain.keypair = pkt.keypair ∧
        plain.nonce = u64le pkt.bytes 8 ∧
        aeadDecrypt key.receiving.key (counterNonce (u64le pkt.bytes 8))
          (pkt.bytes.drop 16) [] = some plain.bytes) := by
  let P : WGWorld → Prop := fun g => (g.dev.bind fun d => d.keypairs[pkt.keypair]?) = some key
  let T : WGWorld → Prop := fun _ => True
  let R : Option RxPacket → WGWorld → Prop := fun result _ => ∀ plain, result = some plain →
    plain.source = pkt.source ∧ plain.peer = pkt.peer ∧ plain.keypair = pkt.keypair ∧
    plain.nonce = u64le pkt.bytes 8 ∧
    aeadDecrypt key.receiving.key (counterNonce (u64le pkt.bytes 8))
      (pkt.bytes.drop 16) [] = some plain.bytes
  have hany {α : Type} (a : WG.M α) : Ensures a T (fun _ => T) := by
    intro _ _ _ _ _ _ _
    trivial
  have hnone (S : WGWorld → Prop) : Ensures (pure none : WG.M (Option RxPacket)) S R := by
    intro g ambient result final after hp hr
    cases hr
    intro plain impossible
    cases impossible
  have hstop (what : String) : Ensures (invariant what : WG.M (Option RxPacket)) T R := by
    intro g ambient result final after hp hr
    simp [invariant, AmbientM.invariant] at hr
    cases hr
  have hread : Ensures (getKeypair pkt.keypair) P (fun actual _ => actual = key) := by
    intro g ambient actual final after hp hr
    cases hd : g.dev with
    | none => simp [P, hd] at hp
    | some d =>
      have resident : d.keypairs[pkt.keypair]? = some key := by simpa [P, hd] using hp
      simp [getKeypair, getDev, hd, resident] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      rfl
  have hkey (f : Keypair → WG.M (Option RxPacket)) (hf : Ensures (f key) T R) :
      Ensures (getKeypair pkt.keypair >>= f) P R := by
    refine ensures_bind _ _ hread ?_
    intro actual g ambient result final after same hr
    subst actual
    exact hf g ambient result final after trivial hr
  change Ensures _ P R
  unfold decryptPacket
  refine ensures_bind _ _
    ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch .decNoKeypair false) P)) ?_
  intro noKeypair
  cases noKeypair with
  | true => exact hnone P
  | false =>
    refine hkey _ ?_
    refine ensures_bind _ _ (hany _) ?_
    intro rejected
    cases rejected with
    | true =>
      refine ensures_bind _ _ (hany _) ?_
      intro current
      refine ensures_bind _ _ (hany _) ?_
      intro _
      exact hnone T
    | false =>
      refine ensures_bind _ _ (hany _) ?_
      intro cowOk
      refine ensures_bind _ _ (hany _) ?_
      intro cowFailed
      cases cowFailed with
      | true => exact hnone T
      | false =>
        refine ensures_bind _ _ (hany _) ?_
        intro sgFailed
        cases sgFailed with
        | true => exact hnone T
        | false =>
          cases decrypted : aeadDecrypt key.receiving.key
              (counterNonce (u64le pkt.bytes 8)) (pkt.bytes.drop 16) [] with
          | none =>
            refine ensures_bind _ _ (hany _) ?_
            intro failed
            cases failed with
            | true => exact hnone T
            | false => exact hstop _
          | some bytes =>
            refine ensures_bind _ _ (hany _) ?_
            intro failed
            cases failed with
            | true => exact hnone T
            | false =>
              refine ensures_bind _ _ (hany _) ?_
              intro trimFailed
              cases trimFailed with
              | true => exact hnone T
              | false =>
                intro g ambient result final after hp hr
                cases hr
                intro plain same
                cases same
                exact ⟨rfl, rfl, rfl, rfl, decrypted⟩

end Leanux.Proofs.WG.Roaming
