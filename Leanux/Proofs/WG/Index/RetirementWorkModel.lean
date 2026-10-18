import Leanux.Proofs.WG.Index.RetirementPaymentSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Leanux.Proofs.Framing Leanux.Proofs.Logged
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

structure RetirementWork (original : DurableHolders) (cs : Ledger)
    (loans retired : Reservations) (w : WGWorld) : Prop where
  account : DuringWork original cs loans w
  configured : ConfiguredIdentity.Inv w
  base : BaseCoherence.Inv w
  covered : ∀ d, w.dev = some d → HashSlotCoverage d
  coherent : ∀ d, w.dev = some d → HashedOwnersCoherent d
  reserved : ∀ d, w.dev = some d → DeadHashedReserved retired d

end Leanux.Proofs.WG.Index
