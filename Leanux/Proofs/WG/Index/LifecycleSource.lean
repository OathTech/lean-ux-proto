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
def initialSnapshot (rlimit : Nat) (net bare foreign stepped seccompChild : Bool)
    (s : Campaign2.Snapshot) : Campaign2.Snapshot :=
  let initialized := Campaign2.core (Runner.initialKernel rlimit net bare foreign stepped seccompChild)
  { s with wg := { s.wg with toCore := initialized } }

theorem initialSnapshot_device (rlimit : Nat) (net bare foreign stepped seccompChild : Bool)
    (s : Campaign2.Snapshot) :
    (initialSnapshot rlimit net bare foreign stepped seccompChild s).wg.device =
      (if net && !bare then some { ifindex := 3, ifname := "wg0" } else none) := rfl

theorem initialSnapshot_safe (rlimit : Nat) (net bare foreign stepped seccompChild : Bool)
    (s : Campaign2.Snapshot) :
    View.TablesSafe (initialSnapshot rlimit net bare foreign stepped seccompChild s) := by
  intro d present
  rw [initialSnapshot_device] at present
  split at present
  · cases present
    exact empty_table_safe _ rfl
  · cases present

theorem wgSetup_device : Returns wgSetup (fun _ => True)
    (fun _ w => w.k.wg = some setupDevice) := by
  intro w _
  exact ⟨(), { w with k := { w.k with wg := some setupDevice } }, rfl, rfl⟩

/-- The original destruction prefix, before free_netdev removes the device.
Its execution may stop; no completion or invariant about its internal states
is assumed by the normal-completion result below. -/
def destructPrefix : M Unit := do
  modifyDev fun d => { d with creatingNet := false, incomingPort := 0 }
  socketReinit none none
  peerRemoveAll
  let d ← getDev
  if !d.sendWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
      || !d.decryptQueue.empty || !d.clearWorkQueue.isEmpty then
    unsupported "wg_destruct with queued work (destroy_workqueue runs it)"
  if !d.handshakeQueue.isEmpty then
    invariant "wg_destruct with handshake messages queued (wg_stop drains the ring)"
  mayHaveSlept
  modifyDev fun d => { d with handshakeQueue := [], handshakeQueueLen := 0 }
  mayHaveSlept
  ratelimiterUninit

theorem wgDestruct_source : wgDestruct = (do
    destructPrefix
    modifyK fun k => { k with wg := none }
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
    (fun _ w => w.k.wg = none) := by
  have hp : Ensures destructPrefix (fun _ => True) (fun _ _ => True) := by
    intro w result final pre run
    trivial
  rw [wgDestruct_source]
  refine ensures_bind _ _ hp ?_
  intro u
  rw [ensures_iff]
  have hr := retireDeviceUnits_device none
  mvcgen [modifyK, hr]

end Leanux.Proofs.WG.Index
