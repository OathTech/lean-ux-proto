import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Index.LifecycleModel
import Leanux.Proofs.WG.Index.LifecycleFrames
import Leanux.Runner

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- Project the original runner initializer's core into an observation.
The remaining WireGuard environment and ambient context are arbitrary; this
does not construct a concrete World or assert a completed runner execution. -/
def initialSnapshot (net bare : Bool)
    (s : Campaign2.Snapshot) : Campaign2.Snapshot :=
  let initialized := Campaign2.core (Runner.initialWG net bare)
  { s with wg := { s.wg with toCore := initialized } }

theorem initialSnapshot_device (net bare : Bool)
    (s : Campaign2.Snapshot) :
    (initialSnapshot net bare s).wg.device =
      (if net && !bare then some { ifindex := 3, ifname := "wg0" } else none) := rfl

theorem initialSnapshot_safe (net bare : Bool)
    (s : Campaign2.Snapshot) :
    View.TablesSafe (initialSnapshot net bare s) := by
  intro d present
  rw [initialSnapshot_device] at present
  split at present
  · cases present
    exact empty_table_safe _ rfl
  · cases present

theorem wgSetup_device : Returns wgSetup (fun _ => True)
    (fun _ w => w.dev = some setupDevice) := by
  intro g ambient _
  exact ⟨(), {g with dev := some setupDevice}, ambient, rfl, rfl⟩

/-- The original destruction prefix, before free_netdev removes the device.
Its execution may stop; no completion or invariant about its internal states
is assumed by the normal-completion result below. -/
def destructPrefix : WG.M Unit := do
  modifyDev fun d => { d with creatingNet := false, incomingPort := 0 }
  socketReinit none none
  peerRemoveAll
  let d ← getDev
  if !d.sendWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
      || !d.decryptQueue.empty || !d.clearWorkQueue.isEmpty then
    unsupported "wg_destruct with queued work (destroy_workqueue runs it)"
  if !d.handshakeQueue.empty then
    invariant "wg_destruct with handshake messages queued (wg_stop drains the ring)"
  mayHaveSlept
  modifyDev fun d => { d with handshakeQueueLen := 0 }
  mayHaveSlept
  ratelimiterUninit

theorem wgDestruct_source : wgDestruct = (do
    destructPrefix
    modify fun g => { g with dev := none }
    retireDeviceUnits) := by
  simp only [wgDestruct, destructPrefix, bind_assoc]
  congr 1
  funext u
  congr 1
  funext u
  congr 1
  funext u
  congr 1
  funext d
  split <;> split <;> simp only [bind_assoc]

/-- Every normally completed destruction reached its original device removal.
This says nothing about stopped prefixes or preservation inside peer removal. -/
theorem wgDestruct_absent : Ensures wgDestruct (fun _ => True)
    (fun _ w => w.dev = none) := by
  have hp : Ensures destructPrefix (fun _ => True) (fun _ _ => True) := by
    intro g ambient result final after pre run
    trivial
  rw [wgDestruct_source]
  refine ensures_bind _ _ hp ?_
  intro _
  refine ensures_bind (Q := fun _ g => g.dev = none) _ _ ?_ ?_
  · intro g ambient result final after pre run
    cases run
    rfl
  · intro _
    exact (ensures_iff _ _ _).mpr (retireDeviceUnits_device none)

end Leanux.Proofs.WG.Index
