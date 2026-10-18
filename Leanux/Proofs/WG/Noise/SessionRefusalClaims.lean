import Leanux.Proofs.WG.Noise.SessionRefusalSource

/-! Total original session refusal paths. Branch observations may grow while
the device and allocation counter are unchanged. -/
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

theorem beginSession_rejected_projected (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (resident : d.peers[pid]? = some p)
    (notCreated : p.handshakeState ≠ HANDSHAKE_CREATED_RESPONSE)
    (notConsumed : p.handshakeState ≠ HANDSHAKE_CONSUMED_RESPONSE) :
    Campaign2.Returns (beginSession pid)
      (fun s => s.wg.device = some d ∧ s.wg.keypairCounter = counter)
      (fun ok s => ok = false ∧ s.wg.device = some d ∧ s.wg.keypairCounter = counter) := by
  intro g ambient pre
  exact ⟨false, g, _, beginSession_rejected_run pid d p resident notCreated notConsumed
    g ambient pre.1, rfl, pre⟩

theorem beginSession_allocation_refused_projected (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (resident : d.peers[pid]? = some p)
    (accepted : p.handshakeState = HANDSHAKE_CREATED_RESPONSE ∨
      p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE)
    (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = 40) (refused : bytes.headD 2 = 0) :
    Campaign2.Returns (beginSession pid)
      (fun s => s.wg.device = some d ∧ s.wg.keypairCounter = counter ∧
        s.ambient.hidden = some ({site := (HiddenSite.alloc .kzallocKeypair).info.id, bytes := bytes} :: rest) ∧
        s.ambient.allocArmed.contains "kzallocKeypair" = true)
      (fun ok s => ok = false ∧ s.wg.device = some d ∧
        s.wg.keypairCounter = counter ∧ s.ambient.hidden = some rest) := by
  intro g ambient pre
  obtain ⟨after, run, remaining⟩ := beginSession_allocation_refused_run pid d p resident accepted
    bytes rest width refused g ambient pre.1 pre.2.2.1 pre.2.2.2
  exact ⟨false, g, after, run, rfl, pre.1, pre.2.1, remaining⟩


end Leanux.Proofs.WG.Noise
