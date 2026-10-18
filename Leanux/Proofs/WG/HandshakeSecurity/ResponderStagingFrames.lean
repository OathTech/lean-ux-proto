import Leanux.Proofs.WG.HandshakeSecurity.ResponderStagingSource
import Leanux.Proofs.WG.Peers.Primitives

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open MaterialOrigin

/-- The complete original prefix through staging selection preserves current
allocation identities, roles and sending keys. Empty queues are included. -/
theorem selectionPrefix_current (pid : PeerId) : SameView current (selectionPrefix pid) := by
  intro initial
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  unfold selectionPrefix at run
  rw [bind_ok_ambient] at run
  obtain ⟨p, u, c, read, rest⟩ := run
  obtain ⟨sameWorld, sameAmbient, _⟩ := Peers.getPeer_current pid w u p a c read
  subst u c
  obtain ⟨d, device, peer⟩ := StagingSelection.peerRead_resident pid ⟨p, w, w, a, a⟩ read
  change w.dev = some d at device
  rw [bind_ok_ambient] at rest
  obtain ⟨empty, u, c, tested, rest⟩ := rest
  have actual : ((branch .stagedEmpty p.staged.isEmpty : WG.M Bool).run w).run a =
      .ok ((p.staged.isEmpty, w), CounterWindow.record a .stagedEmpty p.staged.isEmpty) := rfl
  rw [actual] at tested
  cases tested
  cases isEmpty : p.staged.isEmpty with
  | true =>
    simp only [isEmpty, ↓reduceIte, StateT.run_pure] at rest
    obtain ⟨⟨_, rfl⟩, _⟩ := rest
    exact entry
  | false =>
    simp only [isEmpty, Bool.false_eq_true, ↓reduceIte] at rest
    rw [bind_ok_ambient] at rest
    obtain ⟨ignored, u, c, written, rest⟩ := rest
    cases ignored
    have write : u = {w with dev := some {d with peers := d.peers.insert pid {p with staged := []}}} ∧
        c = CounterWindow.record a .stagedEmpty false := by
      simpa [setPeer, modifyDev, device] using written.symm
    rcases write with ⟨rfl, rfl⟩
    rw [bind_ok_ambient] at rest
    obtain ⟨kp, u, c, borrowed, returned⟩ := rest
    have kept := (hoare_iff_run_ambient _ _ _).mp (keypairGet_current p.keypairCurrent (current w))
      _ _ kp u c (current_peer_write w d pid p {p with staged := []} device peer rfl) borrowed
    simp only [StateT.run_pure] at returned
    obtain ⟨⟨_, rfl⟩, _⟩ := returned
    exact kept.trans entry

theorem selectionPrefix_authorized (pid : PeerId) (confirmed : List Nat) :
    Preserves (Authorized confirmed) (selectionPrefix pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b authorized run
  have frame := (hoare_iff_run_ambient _ _ _).mp (selectionPrefix_current pid (current w))
    w a result v b rfl run
  exact authorized.frame frame

end Leanux.Proofs.WG.HandshakeSecurity.Responder
