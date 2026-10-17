import Leanux.Proofs.WG.Queues.RxKeyProtection

/-! The nullable affiliation invariant supplies the key compatibility used by
RX publication and current-key handoff. Missing keys and cleared owner words
remain admissible; this bridge does not assert initialized affiliation. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG

theorem rxCompatible_of_affiliation {w : WGWorld} (hi : Affiliation.Inv w) :
    RxCompatible w := by
  intro d id pkt hd hp other key ho hk
  have same : other = d := Option.some.inj (ho.symm.trans hd)
  subst other
  have inv : (Affiliation.state d).Inv := hi _ (by simp [Affiliation.view, hd])
  have ref := (inv.rx id pkt.peer pkt.keypair (by simp [Affiliation.state, hp])).2
  exact ref.2 key.internalId key.peer (by simp [Affiliation.state, Affiliation.keyCell, hk])

theorem currentsCompatible_of_affiliation {w : WGWorld} (hi : Affiliation.Inv w) :
    CurrentsCompatible w := by
  intro pid d peer kid hd hp current other key ho hk
  have same : other = d := Option.some.inj (ho.symm.trans hd)
  subst other
  have inv : (Affiliation.state d).Inv := hi _ (by simp [Affiliation.view, hd])
  have ref := inv.slots pid (Affiliation.peerCell peer) kid
    (by simp [Affiliation.state, hp]) (Or.inl current)
  exact ref.2 key.internalId key.peer (by simp [Affiliation.state, Affiliation.keyCell, hk])

theorem keysCompatible_of_affiliation {w : WGWorld} (hi : Affiliation.Inv w) :
    KeysCompatible w :=
  ⟨rxCompatible_of_affiliation hi, currentsCompatible_of_affiliation hi⟩

end Leanux.Proofs.WG.Queues.RxCredits
