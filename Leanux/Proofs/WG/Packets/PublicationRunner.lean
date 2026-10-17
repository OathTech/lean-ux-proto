import Leanux.Proofs.WG.Packets.PublicationSyscalls
import Leanux.Proofs.WG.Origins.RunnerInvariant
import Leanux.Proofs.WG.Queues.JointRunner

/-! Initialized packet certificates on the original receive journal and its
exact projection from the joint runner. All typed traces and both placeholder
modes are covered, including the reached prefix of an indexed Stop. -/
namespace Leanux.Proofs.WG.PublicationRunner
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

/-- The actual fixture and concrete syscall closure establish both owner and
publication checks without a trace-validity or final-invariant premise. -/
theorem executeTrace (trace : Runner.Trace) (placeholders : Bool) :
    PublicationJoint.Safe (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 :=
  RunnerInvariant.executeTraceWith PublicationJoint.Inv PublicationJoint.Safe
    (fun _ _ hi => hi.safe) PublicationOuter.store RxHistory.syscall PublicationSyscalls.syscall
    trace placeholders (PublicationJoint.initial trace.net trace.bare)

theorem publication (trace : Runner.Trace) (placeholders : Bool) :
    PublicationChecks.Safe (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 :=
  (executeTrace trace placeholders).2

/-- This selected consumed occurrence has a strictly earlier decrypt witness
in its actual receive prefix, with the immutable publication certificate. -/
theorem consumed (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (occurrence : Nat) (id : SkbId) (stamp : PacketStamp)
    (receipt : RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .consumed occurrence id stamp receipt :: post) :
    PublicationPollChecks.Certified pre id stamp receipt :=
  publication trace placeholders pre _ post position

/-- Both kinds of checks use the exact RX projection of the same joint run;
no endpoint state is substituted for an event's captured input. -/
theorem joint (trace : Runner.Trace) (placeholders : Bool) :
    PublicationJoint.Safe ((runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).2.filterMap
      RoutingJoint.rxEvent) := by
  have rx := congrArg Prod.snd (RoutingJoint.executeTrace_rx trace placeholders [])
  simp only [List.filterMap_nil] at rx
  rw [← rx]
  exact executeTrace trace placeholders

theorem joint_consumed (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RoutingJoint.Event) (occurrence : Nat) (id : SkbId) (stamp : PacketStamp)
    (receipt : RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).2 =
      pre ++ .rx (.consumed occurrence id stamp receipt) :: post) :
    PublicationPollChecks.Certified (pre.filterMap RoutingJoint.rxEvent) id stamp receipt := by
  apply (joint trace placeholders).2 (pre.filterMap RoutingJoint.rxEvent)
    (.consumed occurrence id stamp receipt) (post.filterMap RoutingJoint.rxEvent)
  simp only [position,List.filterMap_append,List.filterMap_cons,RoutingJoint.rxEvent]

end Leanux.Proofs.WG.PublicationRunner
