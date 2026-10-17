import Leanux.Proofs.WG.Progress.BatchBacklogAcceptance

set_option synthInstance.maxSize 1024
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.Runner

/-- Historical direct-call fixture, without the current runner's FIB boot. -/
def initialWorld : World :=
  { fs := initialFS true
    tasks := initialTasks 32
    wg := { initialWG true with
      portBound := Env.portBound
      fixtureNetDevices := Env.fixtureNetDevices
      dstCacheRecords := true }
    ambient := {
      env := harnessEnv
      timing := Env.timing
      armRecords := true
      hidden := some upRecords} }

def runTwo : Except Stop World := do
  let (_, w) ← (syscall .wgUp).run initialWorld
  let (_, w) ← (skipAmbient : M Unit).run w
  let (_, w) ← (syscall (.wgBatch [.inject 4 32768 cookie64] 100)).run
    {w with ambient := {w.ambient with hidden := some batchRecords}, wg := {w.wg with netRxRaised := false}}
  let (_, w) ← (skipAmbient : M Unit).run w
  return w


def backlog : Option (Nat × Nat × List Nat × Option Nat × Nat × Bool) := do
  let .ok w := runTwo | none
  let d ← w.wg.dev
  return (d.handshakeQueue.count, d.handshakeQueueLen, w.ambient.pendingWork,
    w.ambient.hidden.map List.length, w.ambient.suspended.length, w.wg.netRxRaised)


theorem pendingTrace_backlog : backlog = none := by decide +kernel

def runTwoStop : Option String := match runTwo with
  | .error (.invariant reason) => some reason
  | _ => none

theorem pendingTrace_runTwo_stop : runTwoStop =
    some "wg_batch: the route disagrees with the sender source" := by
  decide +kernel

/-- The old direct fixture fails before its claimed backlog; the real runner
rejection is checked separately in BatchBacklogAcceptance. -/
theorem pendingTrace_runTwo_rejected : runTwo =
    .error (.invariant "wg_batch: the route disagrees with the sender source") := by
  have h := pendingTrace_runTwo_stop
  unfold runTwoStop at h
  cases hr : runTwo with
  | ok value => simp [hr] at h
  | error e =>
    cases e with
    | invariant reason =>
      simp [hr] at h
      subst reason
      rfl
    | outsideDomain site reason => simp [hr] at h
    | hidden reason => simp [hr] at h

end Leanux.Proofs.WG.Progress
