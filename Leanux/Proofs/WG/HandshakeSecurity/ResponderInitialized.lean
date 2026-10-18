import Leanux.Proofs.WG.HandshakeSecurity.ResponderSyscalls
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationUnique

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.Initialized
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

/-- Actual fixture initialization and every concrete syscall actor establish
responder chronology on the existing receive journal, including indexed Stops.
The only remaining source hypotheses are the named H1 slot/material contracts. -/
theorem executeTrace (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges)
    (trace : Runner.Trace) (placeholders : Bool) :
    Joint.Safe (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 :=
  RunnerInvariant.executeTraceWith Joint.Inv Joint.Safe
    (fun _ _ hi => hi.safe) Outer.store RxHistory.syscall (Syscalls.syscall H1 slots)
    trace placeholders (Joint.initial trace.net trace.bare)

theorem consumer_entry (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges)
    (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (occurrence : Nat) (id : SkbId) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .consumed occurrence id stamp r :: post) :
    History.Native (Confirmation.completedLabels pre) r.run.before :=
  (executeTrace H1 slots trace placeholders).2 pre _ post position

/-- A current responder at an actual initialized consumer entry already has
its allocation in the strictly earlier completed-confirmation prefix. This
speaks about a captured entry, without assuming a final state or trace validity. -/
theorem current_has_prior_confirmation (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges)
    (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (occurrence : Nat) (id : SkbId) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .consumed occurrence id stamp r :: post)
    (pid : PeerId) (core : KeyCore) (resident : current r.run.before pid = some core)
    (responder : core.initiator = false) : core.allocation ∈ Confirmation.completedLabels pre :=
  (consumer_entry H1 slots trace placeholders pre post occurrence id stamp r position).1
    pid core resident responder

/-- The actual accepted consumer joins prior responder authorization with its
earlier native AEAD provenance and H1's allocation-labelled uniqueness fact.
The three H1 contracts stay visible. Prefix receipts inside a stopped consumer
and the staged-packet-to-encryption bridge remain separately scoped results. -/
theorem authenticated_history (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges)
    (unique : H1InitializedCompletedConfirmation) (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (occurrence : Nat) (id : SkbId) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .consumed occurrence id stamp r :: post) :
    History.Native (Confirmation.completedLabels pre) r.run.before ∧
    Confirmation.AuthenticatedUnique pre post id r ∧
    Authorized (Confirmation.completedLabels pre ++ (Confirmation.completedLabel r).toList) r.run.after := by
  have entry := consumer_entry H1 slots trace placeholders pre post occurrence id stamp r position
  have authenticated := Confirmation.initialized_authenticated_unique unique trace placeholders
    pre post occurrence id stamp r position
  obtain ⟨_,_,_,_,_,_,_,_,_,valid⟩ :=
    PublicationRunner.consumed trace placeholders pre post occurrence id stamp r position
  exact ⟨entry,authenticated,completed_consumer_history H1 slots _ r valid.1.1 entry.1⟩

end Leanux.Proofs.WG.HandshakeSecurity.Responder.Initialized
