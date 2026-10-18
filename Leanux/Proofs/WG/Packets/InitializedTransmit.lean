import Leanux.Proofs.WG.Packets.ActualTransmit
import Leanux.Proofs.WG.Packets.TransmitRunner
import Leanux.Proofs.WG.Configuration.ParserShape

/-! Initialized outgoing cryptokey routing on the actual runner. All committed
transmit callers use the checked native handoff receipt; no final-state,
per-call authorization or successful trace outcome is assumed. -/
namespace Leanux.Proofs.WG.TransmitJoint.Initialized
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Packets AllowedIps Configuration

def executeTrace (trace : Leanux.Runner.Trace) (placeholders : Bool) : PrefixOuter Event Lean.Json :=
  RxHistory.executeTraceWith Actual.syscall trace placeholders

theorem checks (trace : Leanux.Runner.Trace) (shape : TraceAddressShape trace) (placeholders : Bool) :
    Safe ([],[]) (runPrefixOuter (executeTrace trace placeholders) []).2 :=
  Runner.executeTrace Actual.syscall (Actual.syscall_preserves ([],[])) trace shape placeholders

theorem parsed_checks (json : Lean.Json) (trace : Leanux.Runner.Trace)
    (parsed : Leanux.Runner.parseTrace json = .ok trace) (placeholders : Bool) :
    Safe ([],[]) (runPrefixOuter (executeTrace trace placeholders) []).2 :=
  checks trace (parseTrace_shape json trace parsed) placeholders

theorem projects (trace : Leanux.Runner.Trace) (placeholders : Bool) :
    ProjectsOuter RxTransmit.globalRx id (executeTrace trace placeholders)
      (RxHistory.executeTraceHistory trace placeholders) :=
  Runner.executeTrace_projects Actual.syscall Actual.syscall_projects trace placeholders

theorem erases (trace : Leanux.Runner.Trace) (placeholders : Bool) :
    ErasesOuter (executeTrace trace placeholders) (Leanux.Runner.executeTrace trace placeholders) :=
  Runner.executeTrace_erases Actual.syscall Actual.syscall_projects trace placeholders

theorem checked (trace : Leanux.Runner.Trace) (shape : TraceAddressShape trace) (placeholders : Bool)
    (pre post : List Event) (receipt : Receipt)
    (position : (runPrefixOuter (executeTrace trace placeholders) []).2 = pre ++ .transmit receipt :: post) :
    receipt.Valid ∧ GlobalCompletionState ([],[]) (routes pre) receipt.run.before :=
  Runner.checked Actual.syscall (Actual.syscall_preserves ([],[])) trace shape placeholders pre post receipt position

theorem winner (trace : Leanux.Runner.Trace) (shape : TraceAddressShape trace) (placeholders : Bool)
    (pre post : List Event) (receipt : Receipt)
    (position : (runPrefixOuter (executeTrace trace placeholders) []).2 = pre ++ .transmit receipt :: post) :
    ∃ (pid : PeerId) (v4 : Bool), receipt.run.value = .ok pid ∧
      receipt.family = (if v4 then 4 else 6) ∧
      TxFrontCut (if v4 then 4 else 6) receipt.addr receipt.packets receipt.mtu receipt.run.before
        receipt.run.after receipt.run.ambientBefore receipt.run.ambientAfter pid ∧
      PeerWinner (rootWidth v4) receipt.addr
        (selectedFlat v4 (completionFold (routes pre) ([],[]))) (some pid) ∧
      ∀ pkt ∈ receipt.packets, destinationField (if v4 then 4 else 6) pkt.bytes = receipt.addr :=
  Runner.winner Actual.syscall (Actual.syscall_preserves ([],[])) trace shape placeholders pre post receipt position

theorem parsed_winner (json : Lean.Json) (trace : Leanux.Runner.Trace)
    (parsed : Leanux.Runner.parseTrace json = .ok trace) (placeholders : Bool)
    (pre post : List Event) (receipt : Receipt)
    (position : (runPrefixOuter (executeTrace trace placeholders) []).2 = pre ++ .transmit receipt :: post) :
    ∃ (pid : PeerId) (v4 : Bool), receipt.run.value = .ok pid ∧
      receipt.family = (if v4 then 4 else 6) ∧
      TxFrontCut (if v4 then 4 else 6) receipt.addr receipt.packets receipt.mtu receipt.run.before
        receipt.run.after receipt.run.ambientBefore receipt.run.ambientAfter pid ∧
      PeerWinner (rootWidth v4) receipt.addr
        (selectedFlat v4 (completionFold (routes pre) ([],[]))) (some pid) ∧
      ∀ pkt ∈ receipt.packets, destinationField (if v4 then 4 else 6) pkt.bytes = receipt.addr :=
  winner trace (parseTrace_shape json trace parsed) placeholders pre post receipt position

end Leanux.Proofs.WG.TransmitJoint.Initialized
