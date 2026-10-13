import Leanux.Proofs.Framing.Projection

/-! The complete WireGuard-related part of Kernel. Filesystem helpers may
change files, task work and World records while preserving this view. In
particular, this frame does not assert preservation of pending scheduling. -/
namespace Leanux.Proofs.Framing
open Leanux

@[ext] structure WGKernelView where
  wg : Option WG.Device
  peerCounter : Nat
  keypairCounter : Nat
  nlSock7 : WG.NlSock
  nlSock8 : WG.NlSock
  netIfindexNext : Nat
  ratelimiter : Ratelimiter

def WGKernelView.ofKernel (k : Kernel) : WGKernelView :=
  ⟨k.wg, k.peerCounter, k.keypairCounter, k.nlSock7, k.nlSock8,
    k.netIfindexNext, k.ratelimiter⟩

def wgKernelView (w : World) : WGKernelView := WGKernelView.ofKernel w.k

abbrev SameWGKernel (a : M α) : Prop := SameView wgKernelView a

theorem sameWGKernel_of_sameKernel (h : SameKernel a) : SameWGKernel a :=
  SameView.of_sameKernel WGKernelView.ofKernel h

end Leanux.Proofs.Framing
