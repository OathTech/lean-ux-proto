import Leanux.Proofs.WG.HandshakeSecurity.ResponderIngress
import Leanux.Proofs.WG.HandshakeSecurity.ResponderStagingFrames

/-! Native contracts at the three cuts needed by a common RX/TX observer.
These are source contracts; initialized same-run transport remains separate. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open MaterialOrigin

/-- A completed confirmation extends authorization before its caller can stage
packets. Unlike a completed-consumer label, this fact survives a later Stop. -/
theorem confirmation_native (H1 : H1ResponderCurrentEdges) (pid : PeerId)
    (kid : KeypairId) (confirmed : List Nat) (r : WGRunWitness Bool)
    (valid : r.Valid (receivedWithKeypair pid kid))
    (entry : History.Native confirmed r.before) :
    History.Native (confirmed ++ confirmedAt r.before kid r.value) r.after :=
  ⟨confirmation_authorized H1 pid kid confirmed r.before r.after
      r.ambientBefore r.ambientAfter r.value entry.1 valid,
    (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.receivedWithKeypair_preserves pid kid)
      _ _ _ _ _ entry.2 valid⟩

/-- The original staging selection returns the current slot of the actual peer
read. The intervening staged-queue clear and borrow do not choose another peer. -/
theorem selection_native (pid : PeerId)
    (r : WGRunWitness (Option (Peer × Option KeypairId)))
    (valid : r.Valid (selectionPrefix pid)) (p : Peer) (kid : KeypairId)
    (selected : r.value = some (p, some kid)) :
    ∃ d, r.before.dev = some d ∧ d.peers[pid]? = some p ∧ p.keypairCurrent = some kid := by
  have run := valid
  change ((selectionPrefix pid).run r.before).run r.ambientBefore =
    .ok ((r.value, r.after), r.ambientAfter) at run
  unfold selectionPrefix at run
  rw [bind_ok_ambient] at run
  obtain ⟨read, w, a, readRun, rest⟩ := run
  obtain ⟨rfl, rfl, d, device, peer⟩ := Origins.getPeer_return _ _ _ _ _ _ readRun
  rw [bind_ok_ambient] at rest
  obtain ⟨empty, w, a, test, rest⟩ := rest
  have actual : ((branch .stagedEmpty read.staged.isEmpty : WG.M Bool).run r.before).run
      r.ambientBefore = .ok ((read.staged.isEmpty, r.before),
        CounterWindow.record r.ambientBefore .stagedEmpty read.staged.isEmpty) := rfl
  rw [actual] at test
  cases test
  cases empty : read.staged.isEmpty with
  | true => simp [empty, StateT.run_pure, selected] at rest
  | false =>
    simp only [empty, Bool.false_eq_true, ↓reduceIte] at rest
    rw [bind_ok_ambient] at rest
    obtain ⟨ignored, w, a, _, rest⟩ := rest
    rw [bind_ok_ambient] at rest
    obtain ⟨kp, v, b, borrowed, returned⟩ := rest
    simp only [StateT.run_pure, selected] at returned
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := returned
    exact ⟨d, device, peer, StagingSelection.keypairGet_selected _ _ _ _ _ _ borrowed⟩

/-- Source selection and the resident material read identify the actual current
allocation, role and sending key at staging entry. -/
theorem selection_current (pid : PeerId)
    (r : WGRunWitness (Option (Peer × Option KeypairId)))
    (valid : r.Valid (selectionPrefix pid)) (p : Peer) (kid : KeypairId)
    (selected : r.value = some (p, some kid)) (core : KeyCore)
    (material : pool r.before kid = some core) : current r.before pid = some core := by
  obtain ⟨d, device, peer, slot⟩ := selection_native pid r valid p kid selected
  simpa [current, pool, device, peer, slot] using material

/-- This is a local chronology contract. Its entry authorization must be
transported to the actual shared driver cut, not supplied as a runner premise. -/
theorem selected_responder_confirmed (pid : PeerId)
    (r : WGRunWitness (Option (Peer × Option KeypairId)))
    (valid : r.Valid (selectionPrefix pid)) (p : Peer) (kid : KeypairId)
    (selected : r.value = some (p, some kid)) (core : KeyCore)
    (material : pool r.before kid = some core) (confirmed : List Nat)
    (entry : Authorized confirmed r.before) (responder : core.initiator = false) :
    core.allocation ∈ confirmed :=
  entry pid core (selection_current pid r valid p kid selected core material) responder

/-- Clearing the staged queue and borrowing current retain every resident keys
allocation, direction and sending material; no slot-liveness premise is used. -/
theorem selection_core (pid : PeerId) : SameView pool (selectionPrefix pid) := by
  intro initial
  unfold selectionPrefix
  material_lower
  repeat' core_traffic (fun p => p = initial)

/-- A native material read after selection belongs to the current responder
selected at entry. The prefix itself supplies the material frame. -/
theorem selected_after_material (pid : PeerId)
    (r : WGRunWitness (Option (Peer × Option KeypairId)))
    (valid : r.Valid (selectionPrefix pid)) (p : Peer) (kid : KeypairId)
    (selected : r.value = some (p, some kid)) (core : KeyCore)
    (material : pool r.after kid = some core) (confirmed : List Nat)
    (entry : Authorized confirmed r.before) (responder : core.initiator = false) :
    core.allocation ∈ confirmed := by
  have same := (hoare_iff_run_ambient _ _ _).mp (selection_core pid (pool r.before))
    _ _ _ _ _ rfl valid
  exact selected_responder_confirmed pid r valid p kid selected core (same ▸ material)
    confirmed entry responder

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
