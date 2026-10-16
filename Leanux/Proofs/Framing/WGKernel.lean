import Leanux.Proofs.Framing.Projection

/-! The seven-field WireGuard store projection. Other native WG fields,
including timer and scheduling state, are outside this view. -/
namespace Leanux.Proofs.Framing
open Leanux

@[ext] structure WGStoreView where
  dev : Option WG.Device
  peerCounter : Nat
  keypairCounter : Nat
  nlSock7 : WG.NlSock
  nlSock8 : WG.NlSock
  netIfindexNext : Nat
  ratelimiter : Ratelimiter

def wgStoreView (w : WGWorld) : WGStoreView :=
  ⟨w.dev, w.peerCounter, w.keypairCounter, w.nlSock7, w.nlSock8,
    w.netIfindexNext, w.ratelimiter⟩

abbrev SameWGStore (a : WG.M α) : Prop := SameView wgStoreView a

end Leanux.Proofs.Framing
