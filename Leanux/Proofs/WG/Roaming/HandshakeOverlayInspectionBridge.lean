import Leanux.Proofs.WG.Roaming.HandshakeOverlayTransportSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeOverlay
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- Run one actual observer on the input state, preserving its exact outcome
and attempt journal as data while retaining the inspection entry. -/
def inspect {α : Type} (observed : PrefixM RxEvent α) : Leanux.M (Inspection α) :=
  fun w =>
    let result := runPrefix observed w []
    .ok (⟨Campaign2.Product.observeResult result.1,result.2.filterMap rxAttempt⟩,w)

def observeStep : Leanux.M (Inspection Bool) := inspect receiveStep

def observeSchedule (stack : Option Worker) : Leanux.M (Inspection Unit) :=
  inspect (HandshakeAttemptTransport.schedule receiver stack)

end Leanux.Proofs.WG.Roaming.HandshakeOverlay
