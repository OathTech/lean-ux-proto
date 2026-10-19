import Leanux.Proofs.WG.Roaming.PollAuthenticationSyscallSource
import Leanux.Proofs.WG.Origins.RunnerInvariant

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication.Initialized
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes

theorem initial (net bare : Bool) (w : World)
    (same : wgStoreView w.wg = wgStoreView (Runner.initialWG net bare)) : Reached [] w := by
  refine ⟨PublicationJoint.initial net bare w same,?_⟩
  intro pre n id stamp pkt receipt post impossible
  have length := congrArg List.length impossible
  simp only [List.length_nil,List.length_append,List.length_cons] at length
  omega

/-- Every initialized outcome retains certificates for the reached checks,
including those followed by a consume failure or a later indexed Stop. -/
theorem executeTrace (trace : Runner.Trace) (placeholders : Bool) :
    PublicSafe (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 :=
  RunnerInvariant.executeTraceWith Reached PublicSafe reached_safe reached_wgStore
    RxHistory.syscall Syscalls.syscall trace placeholders (initial trace.net trace.bare)

theorem checkedEndpoint (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (occurrence id : Nat) (stamp : PacketStamp)
    (pkt : RxPacket) (receipt : RunWitness (Option Endpoint))
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .checkedEndpoint occurrence id stamp pkt receipt :: post) :
    Certified pre id stamp pkt receipt :=
  (executeTrace trace placeholders).2 pre occurrence id stamp pkt receipt post position

end Leanux.Proofs.WG.Roaming.PollAuthentication.Initialized
