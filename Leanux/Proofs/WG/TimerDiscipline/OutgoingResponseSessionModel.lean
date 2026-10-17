import Leanux.Proofs.WG.TimerDiscipline.ResponseSessionModel

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2 Noise Roaming Std.Do

/-- The actual MAC-added response and the session stage reached by its sender. -/
structure OutgoingResponseSessionCall where
  message : List UInt8
  session : ResponseSessionCut

def OutgoingResponseSessionObservation (pid : PeerId)
    (outcome : Campaign2.Product.Outcome (Option OutgoingResponseSessionCall)) : Prop :=
  ∃ candidate afterPrefix, outcome = .ok (candidate, afterPrefix) ∧
    ∀ cut, candidate = some cut →
      ResponseSessionFacts pid cut.session ∧ responseSessionEnd cut.session = afterPrefix


end Leanux.Proofs.WG.TimerDiscipline
