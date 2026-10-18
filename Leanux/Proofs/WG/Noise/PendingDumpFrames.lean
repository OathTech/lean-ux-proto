import Leanux.Proofs.WG.Config.DumpInvariantSource
import Leanux.Proofs.WG.Noise.PendingTimerFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingDump
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Std.Do PendingSession

/-- Socket-only writes do not affect the configured identity, nullable key slots,
or pending allocation labels. Reference changes use their concrete contracts. -/
theorem contracts (seen : List Nat) :
    Config.DumpInvariant.Contracts (fun w => NativeInv w seen) where
  stable := by
    intro w v same hi
    have device := congrArg WGStoreView.dev same
    have counter := congrArg WGStoreView.keypairCounter same
    change v.dev = w.dev at device
    change v.keypairCounter = w.keypairCounter at counter
    simpa only [NativeInv,ConfiguredIdentity.Inv,ConfiguredIdentity.InvExcept,
      ConfiguredIdentity.view,CurrentSlots.Inv,Affiliation.view,PendingTickets.view,
      device,counter] using hi
  acquire pid := PendingTimers.peerGet_native pid seen
  release pid := PendingReception.pay pid seen

end Leanux.Proofs.WG.Noise.PendingDump
