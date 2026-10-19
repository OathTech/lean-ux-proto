import Leanux.Proofs.WG.Config.ConfiguredTailClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

theorem psk_base (pid : PeerId) (key : Key) :
    SameView BaseCoherence.view (getPeer pid >>= fun p=>setPeer pid {p with presharedKey:=key}) :=
  ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_read) pid).bind
    (fun p=>(pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_write) pid {p with presharedKey:=key})

end Leanux.Proofs.WG.Config.OwnerConfiguration
