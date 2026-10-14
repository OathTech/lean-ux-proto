import Leanux.Runner

set_option synthInstance.maxSize 1024
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.Runner

def recAt (site : HiddenSite) (bytes : List UInt8) : HiddenRecord :=
  { site := site.info.id, bytes }

def word (n : Nat) : List UInt8 :=
  (List.range 8).map fun i => UInt8.ofNat (n / 256 ^ i % 256)

def cookie64 : List UInt8 := [3, 0, 0, 0] ++ List.replicate 60 0
def upRecords : List HiddenRecord :=
  [recAt .udpPortDraw (word 0), recAt .jiffiesEnd (word 100)]
def batchRecords : List HiddenRecord :=
  [recAt (.sectionStart .netRx) (word 0 ++ word 0),
   recAt (.queued .receiveWorker) (word 1 ++ word 0),
   recAt (.sectionStop .netRx) (word 0), recAt .jiffiesEnd (word 101)]
def pendingTrace : Trace :=
  { id := "campaign2-pending-handshake", ops := #[.wgUp, .wgBatch [.inject 4 32768 cookie64] 100],
    armRecords := true, hidden := some #[upRecords, batchRecords] }

def initialWorld : World :=
  { k := initialKernel 32 true, env := harnessEnv, timing := Env.timing,
    portBound := Env.portBound, fixtureNetDevices := Env.fixtureNetDevices,
    armRecords := true, dstCacheRecords := true, hidden := some upRecords }

def runTwo : Except Stop World := do
  let (_, w) ← (syscall .wgUp).run initialWorld
  let (_, w) ← skipAmbient.run w
  let (_, w) ← (syscall (.wgBatch [.inject 4 32768 cookie64] 100)).run
    { w with hidden := some batchRecords, netRxRaised := false }
  let (_, w) ← skipAmbient.run w
  return w


def accepted : Bool :=
  match executeTrace pendingTrace with
  | .ok _ => true
  | .error _ => false

def backlog : Option (Nat × Nat × List Nat × Option Nat × Nat × Bool) := do
  let .ok w := runTwo | none
  let d ← w.k.wg
  return (d.handshakeQueue.length, d.handshakeQueueLen, w.pendingWork,
    w.hidden.map List.length, w.suspended.length, w.netRxRaised)

theorem pendingTrace_accepted : accepted = true := by decide +kernel

theorem pendingTrace_backlog : backlog = some (1, 1, [1], some 0, 0, false) := by decide +kernel

end Leanux.Proofs.WG.Progress
