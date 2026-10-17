import Leanux.Proofs.WG.Progress.BatchBacklogAcceptance

set_option synthInstance.maxSize 1024
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.Runner

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


def backlog : Option (Nat × Nat × List Nat × Option Nat × Nat × Bool) := do
  let .ok w := runTwo | none
  let d ← w.k.wg
  return (d.handshakeQueue.length, d.handshakeQueueLen, w.pendingWork,
    w.hidden.map List.length, w.suspended.length, w.netRxRaised)


theorem pendingTrace_backlog : backlog = some (1, 1, [1], some 0, 0, false) := by decide +kernel

end Leanux.Proofs.WG.Progress
