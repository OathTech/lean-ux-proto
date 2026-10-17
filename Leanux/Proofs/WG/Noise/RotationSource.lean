import Leanux.Proofs.WG.Noise.RotationEffects
import Leanux.Proofs.WG.Noise.ClearSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Leanux.Proofs.WG.Config Std.Do

/-- Execute only the original ordered peer writes and immediate puts. -/
def rotationExecute (pid : PeerId) : List RotationAction → WG.M Unit
  | [] => pure ()
  | .write change :: rest => do
    modifyPeer pid (fun p => change.apply p)
    rotationExecute pid rest
  | .put key :: rest => do
    keypairPut key true
    rotationExecute pid rest

def rotationSource (pid : PeerId) (newKey : KeypairId) : WG.M Unit := do
  let p ← getPeer pid
  if ← branch .addKeypairInitiator (← getKeypair newKey).iAmTheInitiator then
    if ← branch .addKeypairHasNext p.keypairNext.isSome then
      rotationExecute pid (rotateWithNext p newKey)
    else rotationExecute pid (rotateWithoutNext p newKey)
  else rotationExecute pid (rotateResponder p newKey)

theorem addNewKeypair_rotation_source (pid : PeerId) (newKey : KeypairId) :
    addNewKeypair pid newKey = rotationSource pid newKey := by
  have finish (a : WG.M Unit) : (a >>= fun _ => pure ()) = a := by
    have same : (fun _ : Unit => (pure () : WG.M Unit)) = pure := by
      funext u; cases u; rfl
    rw [same, bind_pure]
  simp only [addNewKeypair, rotationSource, rotateWithNext, rotateWithoutNext,
    rotateResponder, rotationExecute, RotationWrite.apply, finish]
  all_goals rfl

def confirmationSource (pid : PeerId) (received : KeypairId) : WG.M Bool := do
  if ← branch .receivedNotNew ((← getPeer pid).keypairNext != some received) then return false
  if ← branch .receivedChanged ((← getPeer pid).keypairNext != some received) then return false
  let p ← getPeer pid
  rotationExecute pid (confirmationPlan p received)
  return true

theorem receivedWithKeypair_rotation_source (pid : PeerId) (received : KeypairId) :
    receivedWithKeypair pid received = confirmationSource pid received := by
  simp only [receivedWithKeypair, confirmationSource, confirmationPlan, rotationExecute,
    RotationWrite.apply, bind_assoc, pure_bind]

theorem rotationWrite_returns (pid : PeerId) (change : RotationWrite) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (modifyPeer pid change.apply) (fun w => w.dev = some d)
      (fun _ w => w.dev = some (rotationWriteDevice d pid change p)) := by
  intro g ambient device
  refine ⟨(), {g with dev := some (rotationWriteDevice d pid change p)}, ambient, ?_, rfl⟩
  change (((do let q ← getPeer pid; setPeer pid (change.apply q)) : WG.M Unit).run g).run ambient = _
  simp [getPeer, getDev, device, resident, setPeer, modifyDev, rotationWriteDevice]
  rfl

theorem rotationExecute_returns {pid : PeerId} {d final : Device} {actions : List RotationAction}
    (steps : RotationRun pid d actions final) :
    Returns (rotationExecute pid actions) (fun w => w.dev = some d)
      (fun _ w => w.dev = some final) := by
  induction steps with
  | nil d => intro w ambient pre; exact ⟨(), w, ambient, rfl, pre⟩
  | write d final change p rest resident tail ih =>
    exact returns_bind _ _ (rotationWrite_returns pid change d p resident) (fun _ => ih)
  | put d middle final key rest release tail ih =>
    exact returns_bind _ _ (clearPut_returns release) (fun _ => ih)

theorem rotationExecute_effect (pid : PeerId) (d : Device) (p : Peer) (actions : List RotationAction)
    (resident : d.peers[pid]? = some p) :
    Ensures (rotationExecute pid actions) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧ RotationRun pid d actions final) := by
  induction actions generalizing d p with
  | nil =>
    intro w ambient result final after pre run
    change Except.ok (((), w), ambient) = Except.ok ((result, final), after) at run
    cases run
    exact ⟨d, pre, .nil d⟩
  | cons action rest ih =>
    cases action with
    | write change =>
      intro w ambient result final after pre run
      obtain ⟨u, next, nextAmbient, writeRun, device⟩ :=
        rotationWrite_returns pid change d p resident w ambient pre
      change (((modifyPeer pid change.apply).run w).run ambient >>= fun ((_, g), a) =>
        ((rotationExecute pid rest).run g).run a) = _ at run
      rw [writeRun] at run
      obtain ⟨out, post, tail⟩ := ih (rotationWriteDevice d pid change p) (change.apply p)
        (by simp [rotationWriteDevice]) next nextAmbient result final after device run
      exact ⟨out, post, .write d out change p rest resident tail⟩
    | put key =>
      change Ensures (keypairPut key true >>= fun _ => rotationExecute pid rest) _ _
      refine ensures_bind _ _ (clearPut_effect key d) ?_
      intro u w ambient result final after pre run
      obtain ⟨middle, device, release⟩ := pre
      obtain ⟨out, post, tail⟩ := ih middle p (by rw [clearPut_peers release]; exact resident)
        w ambient result final after device run
      exact ⟨out, post, .put d middle out key rest release tail⟩

/-- Constructed from static reference multiplicities, not an input execution witness. -/
theorem rotationExecute_returns_ready (pid : PeerId) (d : Device) (p : Peer) (actions : List RotationAction)
    (resident : d.peers[pid]? = some p) (ready : ClearReady d (rotationReleases actions)) :
    Returns (rotationExecute pid actions) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧ RotationRun pid d actions final) := by
  obtain ⟨final, steps⟩ := rotationRun_exists pid d p actions resident ready
  intro w ambient pre
  obtain ⟨u, after, afterAmbient, run, post⟩ := rotationExecute_returns steps w ambient pre
  exact ⟨u, after, afterAmbient, run, final, post, steps⟩

/-- Normal rotation derives its complete effect from the original execution. -/
theorem addNewKeypair_effect (pid : PeerId) (newKey : KeypairId) (d : Device) (p : Peer) (k : Keypair)
    (resident : d.peers[pid]? = some p) (key : d.keypairs[newKey]? = some k) :
    Ensures (addNewKeypair pid newKey) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧
        RotationRun pid d (rotationPlan p k.iAmTheInitiator newKey) final) := by
  intro w ambient result final after pre run
  rw [addNewKeypair_rotation_source] at run
  let first : Ambient := { ambient with steps := ambient.steps.push ⟨.addKeypairInitiator, k.iAmTheInitiator, none, none, ambient.netRxSection⟩ }
  let selected : Ambient := if k.iAmTheInitiator then
    { first with steps := first.steps.push ⟨.addKeypairHasNext, p.keypairNext.isSome, none, none, first.netRxSection⟩ }
    else first
  have source : ((rotationSource pid newKey).run w).run ambient =
      ((rotationExecute pid (rotationPlan p k.iAmTheInitiator newKey)).run w).run selected := by
    cases mode : k.iAmTheInitiator <;> cases pending : p.keypairNext <;>
      simp [rotationSource, getPeer, getKeypair, getDev, pre, resident, key,
        branch, AmbientM.branch, rotationPlan, mode, pending, selected, first]
    all_goals rfl
  rw [source] at run
  exact rotationExecute_effect pid d p _ resident w selected result final after pre run

theorem addNewKeypair_returns_ready (pid : PeerId) (newKey : KeypairId) (d : Device) (p : Peer) (k : Keypair)
    (resident : d.peers[pid]? = some p) (key : d.keypairs[newKey]? = some k)
    (ready : ClearReady d (rotationReleases (rotationPlan p k.iAmTheInitiator newKey))) :
    Returns (addNewKeypair pid newKey) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧
        RotationRun pid d (rotationPlan p k.iAmTheInitiator newKey) final) := by
  intro w ambient pre
  let first : Ambient := { ambient with steps := ambient.steps.push ⟨.addKeypairInitiator, k.iAmTheInitiator, none, none, ambient.netRxSection⟩ }
  let selected : Ambient := if k.iAmTheInitiator then
    { first with steps := first.steps.push ⟨.addKeypairHasNext, p.keypairNext.isSome, none, none, first.netRxSection⟩ }
    else first
  obtain ⟨u, after, afterAmbient, run, post⟩ :=
    rotationExecute_returns_ready pid d p _ resident ready w selected pre
  refine ⟨u, after, afterAmbient, ?_, post⟩
  rw [addNewKeypair_rotation_source]
  have source : ((rotationSource pid newKey).run w).run ambient =
      ((rotationExecute pid (rotationPlan p k.iAmTheInitiator newKey)).run w).run selected := by
    cases mode : k.iAmTheInitiator <;> cases pending : p.keypairNext <;>
      simp [rotationSource, getPeer, getKeypair, getDev, pre, resident, key,
        branch, AmbientM.branch, rotationPlan, mode, pending, selected, first]
    all_goals rfl
  exact source.trans run

theorem receivedWithKeypair_effect (pid : PeerId) (received : KeypairId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (receivedWithKeypair pid received) (fun w => w.dev = some d)
      (fun ok w => ∃ final, w.dev = some final ∧ ConfirmationEffect pid received d p ok final) := by
  intro w ambient result final after pre run
  rw [receivedWithKeypair_rotation_source] at run
  by_cases matched : p.keypairNext = some received
  · let selected : Ambient := { ambient with steps :=
      (ambient.steps.push ⟨.receivedNotNew, false, none, none, ambient.netRxSection⟩).push ⟨.receivedChanged, false, none, none, ambient.netRxSection⟩ }
    have source : ((confirmationSource pid received).run w).run ambient =
        (fun output => ((true, output.1.2), output.2)) <$>
          ((rotationExecute pid (confirmationPlan p received)).run w).run selected := by
      simp [confirmationSource, getPeer, getDev, pre, resident, branch, AmbientM.branch, matched, selected]
    rw [source] at run
    cases execution : ((rotationExecute pid (confirmationPlan p received)).run w).run selected with
    | error e => rw [execution] at run; cases run
    | ok output =>
      rcases output with ⟨⟨u, next⟩, nextAmbient⟩
      obtain ⟨out, device, steps⟩ := rotationExecute_effect pid d p _ resident
        w selected u next nextAmbient pre execution
      rw [execution] at run
      cases run
      exact ⟨out, device, by simp [ConfirmationEffect, matched, steps]⟩
  · have source : ((confirmationSource pid received).run w).run ambient =
        Except.ok ((false, w), { ambient with steps := ambient.steps.push ⟨.receivedNotNew, p.keypairNext != some received, none, none, ambient.netRxSection⟩ }) := by
      simp [confirmationSource, getPeer, getDev, pre, resident, branch, AmbientM.branch, matched]
      rfl
    rw [source] at run
    cases run
    exact ⟨d, pre, by simp [ConfirmationEffect, matched]⟩

theorem receivedWithKeypair_returns_ready (pid : PeerId) (received : KeypairId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (ready : p.keypairNext = some received → ClearReady d [p.keypairPrevious]) :
    Returns (receivedWithKeypair pid received) (fun w => w.dev = some d)
      (fun ok w => ∃ final, w.dev = some final ∧ ConfirmationEffect pid received d p ok final) := by
  intro w ambient pre
  rw [receivedWithKeypair_rotation_source]
  by_cases matched : p.keypairNext = some received
  · let selected : Ambient := { ambient with steps :=
      (ambient.steps.push ⟨.receivedNotNew, false, none, none, ambient.netRxSection⟩).push ⟨.receivedChanged, false, none, none, ambient.netRxSection⟩ }
    obtain ⟨u, after, afterAmbient, run, out, device, steps⟩ :=
      rotationExecute_returns_ready pid d p (confirmationPlan p received) resident (ready matched)
        w selected pre
    refine ⟨true, after, afterAmbient, ?_, out, device, ?_⟩
    · have source : ((confirmationSource pid received).run w).run ambient =
          (fun output => ((true, output.1.2), output.2)) <$>
            ((rotationExecute pid (confirmationPlan p received)).run w).run selected := by
        simp [confirmationSource, getPeer, getDev, pre, resident, branch, AmbientM.branch, matched, selected]
      rw [source, run]
      rfl
    · simp [ConfirmationEffect, matched, steps]
  · refine ⟨false, w, { ambient with steps := ambient.steps.push ⟨.receivedNotNew, p.keypairNext != some received, none, none, ambient.netRxSection⟩ }, ?_, d, pre, ?_⟩
    · simp [confirmationSource, getPeer, getDev, pre, resident, branch, AmbientM.branch, matched]
      rfl
    · simp [ConfirmationEffect, matched]

end Leanux.Proofs.WG.Noise
