import Leanux.Proofs.WG.Origins.ShapedRunnerInvariant
import Leanux.Proofs.WG.Packets.OldRx
import Leanux.Proofs.WG.Packets.TransmitStack
import Leanux.Proofs.WG.Configuration.RunnerRouting

/-! The existing initialized runner applied to an actual transmit-observing
syscall family. Only per-call preservation and correspondence are parameters;
no initialized outcome or authorization result is assumed. -/
namespace Leanux.Proofs.WG.TransmitJoint.Runner
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Packets AllowedIps Configuration

/-- Only the original seven-field WG initialization premise is needed.
Unrelated product components and native Ambient inputs remain unrestricted. -/
theorem initial (trace : Leanux.Runner.Trace) (w : World)
    (same : wgStoreView w.wg = wgStoreView (Leanux.Runner.initialWG trace.net trace.bare)) :
    Inv ([],[]) [] w := by
  refine ⟨Configuration.global_initial trace w same,?_⟩
  intro pre event post impossible
  cases pre <;> cases impossible

/-- Every successful or indexed-Stop result retains all strict-prefix
transmit checks, from the actual fixture and shaped operations in this trace. -/
theorem executeTrace (call : Syscall → PrefixM Event Int)
    (calls : ∀ c, SyscallAddressShape c → PrefixPreserves (Inv ([],[])) (Safe ([],[])) (call c))
    (trace : Leanux.Runner.Trace) (shape : TraceAddressShape trace) (placeholders : Bool) :
    Safe ([],[]) (runPrefixOuter (RxHistory.executeTraceWith call trace placeholders) []).2 :=
  RunnerInvariant.Shaped.executeTraceWith (Inv ([],[])) (Safe ([],[]))
    (fun _ _ hi => hi.safe) Inv.store SyscallAddressShape call calls trace
    (fun op member results ends index => toSyscall_shape results ends index op (shape op member))
    placeholders (initial trace)

/-- Projection retains the original JSON, exact indexed Stop and every old RX
constructor, for arbitrary incoming histories and both placeholder modes. -/
theorem executeTrace_projects (call : Syscall → PrefixM Event Int)
    (calls : ∀ c, ProjectsPrefix RxTransmit.globalRx id (call c) (RxHistory.syscall c))
    (trace : Leanux.Runner.Trace) (placeholders : Bool) :
    ProjectsOuter RxTransmit.globalRx id (RxHistory.executeTraceWith call trace placeholders)
      (RxHistory.executeTraceHistory trace placeholders) := by
  change ProjectsOuter RxTransmit.globalRx id (RxHistory.executeTraceWith call trace placeholders)
    (RxHistory.executeTraceWith RxHistory.syscall trace placeholders)
  rw [RoutingJoint.executeTrace_rx_factor,RoutingJoint.executeTrace_rx_factor]
  exact RoutingJoint.executeTraceWith_projects RxTransmit.globalRx id call RxHistory.syscall
    (fun j _ => j) (fun j _ => j) calls (fun _ _ => rfl) trace placeholders

/-- The actual executable runner has the same JSON or indexed Stop.
The claim does not require a normal return or a valid routing trace. -/
theorem executeTrace_erases (call : Syscall → PrefixM Event Int)
    (calls : ∀ c, ProjectsPrefix RxTransmit.globalRx id (call c) (RxHistory.syscall c))
    (trace : Leanux.Runner.Trace) (placeholders : Bool) :
    ErasesOuter (RxHistory.executeTraceWith call trace placeholders)
      (Leanux.Runner.executeTrace trace placeholders) := by
  intro h
  have projected := congrArg Prod.fst (executeTrace_projects call calls trace placeholders h)
  have original := RxHistory.executeTraceHistory_erases trace placeholders (h.filterMap RxTransmit.globalRx)
  have same := projected.symm.trans original
  cases result : (runPrefixOuter (RxHistory.executeTraceWith call trace placeholders) h).1 <;>
    simpa only [result,Except.map,id_eq] using same

/-- A selected occurrence uses its own captured native front and strict
routing prefix, even if the enclosing trace later stops. -/
theorem checked (call : Syscall → PrefixM Event Int)
    (calls : ∀ c, SyscallAddressShape c → PrefixPreserves (Inv ([],[])) (Safe ([],[])) (call c))
    (trace : Leanux.Runner.Trace) (shape : TraceAddressShape trace) (placeholders : Bool)
    (pre post : List Event) (r : Receipt)
    (position : (runPrefixOuter (RxHistory.executeTraceWith call trace placeholders) []).2 =
      pre ++ .transmit r :: post) :
    r.Valid ∧ GlobalCompletionState ([],[]) (routes pre) r.run.before :=
  (executeTrace call calls trace shape placeholders).2 pre (.transmit r) post position

/-- The actual handoff selected the longest-prefix owner at its captured
entry. Later configuration changes and cleanup cannot rewrite this prefix. -/
theorem winner (call : Syscall → PrefixM Event Int)
    (calls : ∀ c, SyscallAddressShape c → PrefixPreserves (Inv ([],[])) (Safe ([],[])) (call c))
    (trace : Leanux.Runner.Trace) (shape : TraceAddressShape trace) (placeholders : Bool)
    (pre post : List Event) (r : Receipt)
    (position : (runPrefixOuter (RxHistory.executeTraceWith call trace placeholders) []).2 =
      pre ++ .transmit r :: post) :
    ∃ (pid : PeerId) (v4 : Bool), r.run.value = .ok pid ∧
      r.family = (if v4 then 4 else 6) ∧
      TxFrontCut (if v4 then 4 else 6) r.addr r.packets r.mtu r.run.before
        r.run.after r.run.ambientBefore r.run.ambientAfter pid ∧
      PeerWinner (rootWidth v4) r.addr
        (selectedFlat v4 (completionFold (routes pre) ([],[]))) (some pid) ∧
      ∀ pkt ∈ r.packets, destinationField (if v4 then 4 else 6) pkt.bytes = r.addr :=
  (executeTrace call calls trace shape placeholders).2.winner pre post r position

end Leanux.Proofs.WG.TransmitJoint.Runner
