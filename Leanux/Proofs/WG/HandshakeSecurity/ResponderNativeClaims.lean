import Leanux.Proofs.WG.HandshakeSecurity.ResponderH1

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem session_authorized (H1 : H1ResponderCurrentEdges) (pid : PeerId) (confirmed : List Nat)
    (w v : WGWorld) (a b : Ambient) (result : Bool)
    (entry : Authorized confirmed w) (bounded : CurrentSlots.Inv w)
    (run : ((beginSession pid).run w).run a = .ok ((result, v), b)) : Authorized confirmed v := by
  intro q core resident responder
  rcases H1.session pid w v a b result bounded run q core resident with old | initiator
  · exact entry q core old responder
  · rw [responder] at initiator
    cases initiator

theorem confirmation_authorized (H1 : H1ResponderCurrentEdges) (pid : PeerId)
    (kid : KeypairId) (confirmed : List Nat) (w v : WGWorld) (a b : Ambient) (result : Bool)
    (entry : Authorized confirmed w)
    (run : ((receivedWithKeypair pid kid).run w).run a = .ok ((result, v), b)) :
    Authorized (confirmed ++ confirmedAt w kid result) v := by
  intro q core resident responder
  rcases H1.confirmation pid kid w v a b result run q core resident with old | promoted
  · exact List.mem_append.mpr (Or.inl (entry q core old responder))
  · obtain ⟨_, accepted, selected⟩ := promoted
    apply List.mem_append.mpr
    right
    simp [confirmedAt, accepted, selected]

theorem clear_authorized (H1 : H1ResponderCurrentEdges) (pid : PeerId) (confirmed : List Nat)
    (w v : WGWorld) (a b : Ambient) (entry : Authorized confirmed w)
    (run : ((keypairsClear pid).run w).run a = .ok (((), v), b)) : Authorized confirmed v := by
  intro q core resident responder
  exact entry q core (H1.clear pid w v a b run q core resident) responder

end Leanux.Proofs.WG.HandshakeSecurity.Responder
