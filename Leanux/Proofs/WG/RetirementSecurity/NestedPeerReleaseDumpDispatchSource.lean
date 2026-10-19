import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpSource
import Leanux.Proofs.WG.Queues.JointNetlink

/-! The three original dump syscall arms expose their dump callbacks while
retaining socket references, allocation cuts, autobind and output order. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged Configuration

def dumpDispatchWith {m : Type → Type} [Monad m]
    (step : {α : Type} → Leanux.M α → m α)
    (device : DeviceRef → m (Except Int Lean.Json))
    (start : Nat → DeviceRef → m Unit) (receive : Nat → m (Option (List NlMessage))) :
    Syscall → m Int
  | .wgGet ref => netlinkRequestWith step do
    match ← device ref with
    | .error err => return err
    | .ok value =>
      step (modifyAmbient fun w => { w with extraOut := [("device",value)] })
      return 0
  | .wgGetStart ref => socketCallOnWith step DUMP_FD do
    step (skipCut allocCuts)
    let sock ← step (liftWG (getNlSock DUMP_FD))
    if !sock.bound then
      step (skipCutExactly .netlinkAutobindPort 1 allocCuts)
      step (liftWG (setNlSock DUMP_FD {sock with bound := true}))
    start DUMP_FD ref
    step (skipCut allocCuts)
    return 0
  | .wgGetRecv => socketCallOnWith step DUMP_FD do
    step (skipCut allocCuts)
    let some messages ← receive DUMP_FD
      | step (Leanux.unsupported "wg_get_recv with nothing queued (-EAGAIN): no WireGuard code runs")
    step (skipCut allocCuts)
    if messages.all (· matches .done ..) then
      step (Leanux.unsupported "wg_get_recv popping a lone NLMSG_DONE: no WireGuard code runs")
    step (modifyAmbient fun w => { w with extraOut := [("messages", Lean.Json.arr (messages.map (·.toJson)).toArray)] })
    return 0
  | call => step (Leanux.dispatch call)

def dumpDispatch (o : Ops (WGPrefix E)) : Syscall → PrefixM E Int :=
  dumpDispatchWith liftPrefix
    (fun ref => liftWGObserver (dumpDeviceWith o ref))
    (fun fd ref => liftWGObserver (dumpStartWith o fd ref))
    (fun fd => liftWGObserver (dumpReceiveWith o fd))

theorem dumpDispatch_native (call : Syscall) :
    dumpDispatchWith (fun a => a) (fun ref => liftWG (wgGetDevice ref))
      (fun fd ref => liftWG (netlinkDumpStart fd ref))
      (fun fd => liftWG (netlinkRecvmsg fd)) call = Leanux.dispatch call := by
  cases call <;> rfl

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
