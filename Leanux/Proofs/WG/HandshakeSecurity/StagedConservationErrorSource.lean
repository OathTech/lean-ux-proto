import Leanux.Proofs.WG.Packets.TxFront
import Leanux.Proofs.Logged.NativeCapture

/-! The actual error notification is followed by one invocation-level error charge. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Packets Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

def errors (w : WGWorld) : Option Nat := w.dev.map Device.txErrors

def errorNotify (family : Nat) (first : Packet) : WG.M Unit := do
  if !(← branch .xmitErrorInet (family == 4)) then _ ← branch .xmitErrorInet6 (family == 6)
  let drawn ← skipCutSites ([.icmpCredit, .ipIdentKey, .ipIdentReserve, .flowHashSecret] ++ allocCuts)
  let mut sent := drawn.contains (HiddenSite.icmpCredit).info.id
  if family == 4 && sent then
    let src := ((first.bytes.drop 12).take 4).foldl (fun acc b => acc * 256 + b.toNat) 0
    match ← Net.routeOutput4 0 src with
    | .error _ => sent := false
    | .ok _ =>
      _ ← Net.Fib.inetDevAddrType (some WG0_IFINDEX) src
      Net.neighbourClassify LO_IFINDEX
  loopbackSend [] sent

theorem error_factor (family : Nat) (first : Packet) (ret : Int) :
    txError family first ret = (do
      errorNotify family first
      modifyDev fun d => {d with txErrors := d.txErrors + 1}
      pure ret) := by
  unfold txError errorNotify
  simp only [bind_assoc]
  repeat' first
    | rfl
    | (apply congrArg; funext x)
    | (split <;> simp only [bind_assoc])


end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
