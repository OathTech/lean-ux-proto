import Leanux.Proofs.WG.AuthenticatedEffects.TransportSyscalls
import Leanux.Proofs.WG.Origins.RunnerInvariant

/-! Initialized pre-consume authentication provenance on the original runner's
persistent receive journal, including internally stopped consumers. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportInitialized
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

/-- Every typed trace and both placeholder modes start from the actual fixture.
No valid-trace, successful-return or caller-publication hypothesis is required. -/
theorem executeTrace (trace : Runner.Trace) (placeholders : Bool) :
    TransportChecks.Safe (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 :=
  RunnerInvariant.executeTraceWith TransportChecks.Inv TransportChecks.Safe
    (fun _ _ hi => hi.2) TransportOuter.store RxHistory.syscall TransportSyscalls.syscall
    trace placeholders (TransportChecks.initial trace.net trace.bare)

/-- The selected existing replay receipt refers to an earlier actual native
AEAD success in this same initialized execution, before consumer effects. -/
theorem replay_entry (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (occurrence id : Nat) (stamp : PacketStamp)
    (pkt : RxPacket) (r : RunWitness Bool)
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .checkedCounter occurrence id stamp pkt r :: post) :
    TransportAuthenticatedEntry.Certified pre id stamp pkt r :=
  executeTrace trace placeholders pre _ post position

end Leanux.Proofs.WG.AuthenticatedEffects.TransportInitialized
