import Leanux.Proofs.WG.Noise.RotationEffects
import Leanux.Proofs.WG.Noise.ClearSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Leanux.Proofs.WG.Config Std.Do

/-- Execute only the original ordered peer writes and immediate puts. -/
def rotationExecute (pid : PeerId) : List RotationAction → M Unit
  | [] => pure ()
  | .write change :: rest => do
    modifyPeer pid (fun p => change.apply p)
    rotationExecute pid rest
  | .put key :: rest => do
    keypairPut key true
    rotationExecute pid rest

def rotationSource (pid : PeerId) (newKey : KeypairId) : M Unit := do
  let p ← getPeer pid
  if ← branch .addKeypairInitiator (← getKeypair newKey).iAmTheInitiator then
    if ← branch .addKeypairHasNext p.keypairNext.isSome then
      rotationExecute pid (rotateWithNext p newKey)
    else rotationExecute pid (rotateWithoutNext p newKey)
  else rotationExecute pid (rotateResponder p newKey)

theorem addNewKeypair_rotation_source (pid : PeerId) (newKey : KeypairId) :
    addNewKeypair pid newKey = rotationSource pid newKey := by
  have distribute {α β : Type} (q : Prop) [Decidable q] (a b : M α) (f : α → M β) :
      ((if q then a else b) >>= f) = (if q then a >>= f else b >>= f) := by
    split <;> rfl
  have finish (a : M Unit) : (a >>= fun _ => pure ()) = a := by
    have same : (fun _ : Unit => (pure () : M Unit)) = pure := by
      funext u; cases u; rfl
    rw [same, bind_pure]
  simp only [addNewKeypair, rotationSource, rotateWithNext, rotateWithoutNext,
    rotateResponder, rotationExecute, RotationWrite.apply, bind_assoc, pure_bind,
    bind_pure, distribute, finish]
  all_goals rfl

def confirmationSource (pid : PeerId) (received : KeypairId) : M Bool := do
  if ← branch .receivedNotNew ((← getPeer pid).keypairNext != some received) then return false
  if ← branch .receivedChanged ((← getPeer pid).keypairNext != some received) then return false
  let p ← getPeer pid
  rotationExecute pid (confirmationPlan p received)
  return true

theorem receivedWithKeypair_rotation_source (pid : PeerId) (received : KeypairId) :
    receivedWithKeypair pid received = confirmationSource pid received := by
  simp only [receivedWithKeypair, confirmationSource, confirmationPlan, rotationExecute,
    RotationWrite.apply, bind_assoc, pure_bind, bind_pure]

theorem rotationWrite_returns (pid : PeerId) (change : RotationWrite) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (modifyPeer pid change.apply) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (rotationWriteDevice d pid change p)) := by
  rw [returns_iff]
  noise_vcgen [_private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [rotationWriteDevice]

theorem rotationExecute_returns {pid : PeerId} {d final : Device} {actions : List RotationAction}
    (steps : RotationRun pid d actions final) :
    Returns (rotationExecute pid actions) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some final) := by
  induction steps with
  | nil d => intro w pre; exact ⟨(), w, rfl, pre⟩
  | write d final change p rest resident tail ih =>
    exact returns_bind _ _ (rotationWrite_returns pid change d p resident) (fun _ => ih)
  | put d middle final key rest release tail ih =>
    exact returns_bind _ _ (clearPut_returns release) (fun _ => ih)

theorem rotationExecute_effect (pid : PeerId) (d : Device) (p : Peer) (actions : List RotationAction)
    (resident : d.peers[pid]? = some p) :
    Ensures (rotationExecute pid actions) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ RotationRun pid d actions final) := by
  induction actions generalizing d p with
  | nil =>
    intro w result final pre run
    change Except.ok ((), w) = Except.ok (result, final) at run
    cases run
    exact ⟨d, pre, .nil d⟩
  | cons action rest ih =>
    cases action with
    | write change =>
      intro w result final pre run
      obtain ⟨u, after, writeRun, device⟩ := rotationWrite_returns pid change d p resident w pre
      simp only [rotationExecute, StateT.run_bind, writeRun] at run
      obtain ⟨out, post, tail⟩ := ih (rotationWriteDevice d pid change p) (change.apply p)
        (by simp [rotationWriteDevice]) after result final device run
      exact ⟨out, post, .write d out change p rest resident tail⟩
    | put key =>
      change Ensures (keypairPut key true >>= fun _ => rotationExecute pid rest) _ _
      refine ensures_bind _ _ (clearPut_effect key d) ?_
      intro u w result final pre run
      obtain ⟨middle, device, release⟩ := pre
      obtain ⟨out, post, tail⟩ := ih middle p (by rw [clearPut_peers release]; exact resident)
        w result final device run
      exact ⟨out, post, .put d middle out key rest release tail⟩

/-- Constructed from static reference multiplicities, not an input execution witness. -/
theorem rotationExecute_returns_ready (pid : PeerId) (d : Device) (p : Peer) (actions : List RotationAction)
    (resident : d.peers[pid]? = some p) (ready : ClearReady d (rotationReleases actions)) :
    Returns (rotationExecute pid actions) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ RotationRun pid d actions final) := by
  obtain ⟨final, steps⟩ := rotationRun_exists pid d p actions resident ready
  intro w pre
  obtain ⟨u, after, run, post⟩ := rotationExecute_returns steps w pre
  exact ⟨u, after, run, final, post, steps⟩

/-- Normal rotation derives its complete effect from the original execution. -/
theorem addNewKeypair_effect (pid : PeerId) (newKey : KeypairId) (d : Device) (p : Peer) (k : Keypair)
    (resident : d.peers[pid]? = some p) (key : d.keypairs[newKey]? = some k) :
    Ensures (addNewKeypair pid newKey) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        RotationRun pid d (rotationPlan p k.iAmTheInitiator newKey) final) := by
  have he := fun actions => (ensures_iff _ _ _).mp (rotationExecute_effect pid d p actions resident)
  rw [addNewKeypair_rotation_source, ensures_iff]
  mvcgen [rotationSource, getPeer, getKeypair, getDev, getK, branch, invariant, he]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [rotationPlan]

theorem addNewKeypair_returns_ready (pid : PeerId) (newKey : KeypairId) (d : Device) (p : Peer) (k : Keypair)
    (resident : d.peers[pid]? = some p) (key : d.keypairs[newKey]? = some k)
    (ready : ClearReady d (rotationReleases (rotationPlan p k.iAmTheInitiator newKey))) :
    Returns (addNewKeypair pid newKey) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        RotationRun pid d (rotationPlan p k.iAmTheInitiator newKey) final) := by
  have he := (returns_iff _ _ _).mp
    (rotationExecute_returns_ready pid d p (rotationPlan p k.iAmTheInitiator newKey) resident ready)
  rw [addNewKeypair_rotation_source, returns_iff]
  cases mode : k.iAmTheInitiator <;> cases pending : p.keypairNext <;>
    simp only [rotationPlan, mode, pending, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, if_false, if_true] at he ⊢
  all_goals mvcgen [rotationSource, getPeer, getKeypair, getDev, getK, branch, invariant, he]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals exact he _ (by assumption)

theorem receivedWithKeypair_effect (pid : PeerId) (received : KeypairId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (receivedWithKeypair pid received) (fun w => w.k.wg = some d)
      (fun ok w => ∃ final, w.k.wg = some final ∧ ConfirmationEffect pid received d p ok final) := by
  have he := (ensures_iff _ _ _).mp (rotationExecute_effect pid d p (confirmationPlan p received) resident)
  rw [receivedWithKeypair_rotation_source, ensures_iff]
  mvcgen [confirmationSource, getPeer, getDev, getK, branch, invariant, he]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [ConfirmationEffect]
  all_goals exact he _ (by assumption)

theorem receivedWithKeypair_returns_ready (pid : PeerId) (received : KeypairId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (ready : p.keypairNext = some received → ClearReady d [p.keypairPrevious]) :
    Returns (receivedWithKeypair pid received) (fun w => w.k.wg = some d)
      (fun ok w => ∃ final, w.k.wg = some final ∧ ConfirmationEffect pid received d p ok final) := by
  by_cases matched : p.keypairNext = some received
  · have he := (returns_iff _ _ _).mp
      (rotationExecute_returns_ready pid d p (confirmationPlan p received) resident (ready matched))
    rw [receivedWithKeypair_rotation_source, returns_iff]
    mvcgen [confirmationSource, getPeer, getDev, getK, branch, invariant, he]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [ConfirmationEffect]
    all_goals exact he _ (by assumption)
  · rw [receivedWithKeypair_rotation_source, returns_iff]
    mvcgen [confirmationSource, getPeer, getDev, getK, branch, invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [ConfirmationEffect]

end Leanux.Proofs.WG.Noise
