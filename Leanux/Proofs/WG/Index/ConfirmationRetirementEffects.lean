import Leanux.Proofs.WG.Index.RetirementSessionEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Queues.RxCredits

/-- Confirmation only rotates existing slots and releases displaced keys;
its actual effect creates no new dead hashed-owner obligation. -/
theorem confirmationEffect_deadHashedReserved (retired : Reservations)
    (pid : PeerId) (received : KeypairId) (d final : Device) (p : Peer) (ok : Bool)
    (reserved : DeadHashedReserved retired d)
    (effect : ConfirmationEffect pid received d p ok final) :
    DeadHashedReserved retired final := by
  by_cases matched : p.keypairNext = some received
  · simp only [ConfirmationEffect,matched,↓reduceIte] at effect
    exact rotationRun_deadHashedReserved effect.2 reserved
  · simp only [ConfirmationEffect,matched,↓reduceIte] at effect
    simpa only [effect.2] using reserved

end Leanux.Proofs.WG.Index
