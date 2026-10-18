import Leanux.Proofs.WG.HandshakeSecurity.ResponderProjection
import Leanux.Proofs.WG.Queues.CurrentSlots

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG

namespace Responder

def keyCoreAt (w : WGWorld) (kid : KeypairId) : Option KeyCore := do
  let d ← w.dev
  (d.keypairs[kid]?).map keyCore

def confirmedAt (w : WGWorld) (kid : KeypairId) (accepted : Bool) : List Nat :=
  if accepted then ((keyCoreAt w kid).map (·.allocation)).toList else []

end Responder

/-- Required source projections of campaign 2 H1's `beginSession_effect`,
`receivedWithKeypair_effect` and `keypairsClear_effect`. The session clause also
uses C1's three-slot bounds to exclude overwriting a currently selected slot
at the allocation frontier. These are local, history-free material/slot
contracts; they are explicit premises, not imported campaign-2 theorems and
not a claim that initialized responder chronology has already been proved.

Only a session's initiator key may newly occupy current. Confirmation may
introduce its received allocation at the selected peer. Deletion is allowed
throughout; neither numeric slot residency nor reference readiness is assumed. -/
structure H1ResponderCurrentEdges : Prop where
  session : ∀ (pid : PeerId) (w v : WGWorld) (a b : Ambient) (result : Bool),
    CurrentSlots.Inv w →
    ((beginSession pid).run w).run a = .ok ((result, v), b) →
    ∀ q core, Responder.current v q = some core →
      Responder.current w q = some core ∨ core.initiator = true
  confirmation : ∀ (pid : PeerId) (kid : KeypairId) (w v : WGWorld)
    (a b : Ambient) (result : Bool),
    ((receivedWithKeypair pid kid).run w).run a = .ok ((result, v), b) →
    ∀ q core, Responder.current v q = some core →
      Responder.current w q = some core ∨
        (q = pid ∧ result = true ∧ Responder.keyCoreAt w kid = some core)
  clear : ∀ (pid : PeerId) (w v : WGWorld) (a b : Ambient),
    ((keypairsClear pid).run w).run a = .ok (((), v), b) →
    ∀ q core, Responder.current v q = some core → Responder.current w q = some core

end Leanux.Proofs.WG.HandshakeSecurity
