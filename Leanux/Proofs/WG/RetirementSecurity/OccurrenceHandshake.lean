import Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshakeFrames
import Leanux.Proofs.WG.Lifetimes.HandshakeCalls

/-! Native Noise helpers preserve the concrete TX ownership/phase invariant.
Allocation freshness is discharged by the independent campaign-1 observer;
no key-reference account or pending-queue separation premise is imported. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem call (call : HandshakeCall) :
    Preserves (OccurrenceStack.Ready locals active) call.original := by
  apply RxPollOccurrences.join call.erases call.allocation
  cases call with
  | createInitiation pid =>
    exact occurrence_passive (OccurrenceKeys.create_initiation_wire pid)
      (OccurrenceKeys.create_initiation_queues pid)
  | createResponse pid =>
    exact occurrence_passive (OccurrenceKeys.create_response_wire pid)
      (OccurrenceKeys.create_response_queues pid)
  | consumeInitiation msg =>
    exact occurrences_queueContents (consume_initiation_wire msg)
      (consume_initiation_contents msg)
  | consumeResponse msg =>
    exact occurrences_queueContents (consume_response_wire msg)
      (consume_response_contents msg)
  | addMac pid msg =>
    exact occurrence_passive (OccurrenceKeys.add_mac_wire pid msg)
      (OccurrenceKeys.add_mac_queues pid msg)

theorem session (pid : PeerId) :
    Preserves (OccurrenceStack.Ready locals active) (beginSession pid) :=
  RxPollOccurrences.join (beginSessionPrefix_erases pid) (beginSessionPrefix_allocation pid)
    (occurrence_passive (OccurrenceKeys.session_wire pid) (OccurrenceKeys.session_queues pid))

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
