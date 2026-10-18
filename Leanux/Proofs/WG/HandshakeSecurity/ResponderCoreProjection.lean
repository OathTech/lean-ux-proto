import Leanux.Proofs.WG.HandshakeSecurity.ResponderProjection

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

abbrev Pool := KeypairId → Option KeyCore
def pool (w : WGWorld) : Pool := fun kid => (w.dev.bind fun d => d.keypairs[kid]?).map keyCore
def Retains (before after : Pool) : Prop := ∀ kid core, after kid = some core → before kid = some core

theorem Retains.refl (p : Pool) : Retains p p := fun _ _ h => h
theorem Retains.trans (a : Retains p q) (b : Retains q r) : Retains p r :=
  fun kid core h => a kid core (b kid core h)

abbrev CoreRetains (a : WG.M α) := ProjectedAction pool Retains a

theorem CoreRetains.wp (h : CoreRetains a) (initial : Pool) :
    Preserves (fun w => Retains initial (pool w)) a :=
  ProjectedAction.wp h (Retains initial) (fun _ _ step prior => prior.trans step)

end Leanux.Proofs.WG.HandshakeSecurity.Responder
