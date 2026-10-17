import Leanux.Proofs.WG.Noise.RotationSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

theorem rotation_ordered (pid : PeerId) (newKey : KeypairId)
    (d : Device) (p : Peer) (k : Keypair)
    (resident : d.peers[pid]? = some p) (key : d.keypairs[newKey]? = some k) :
    Campaign2.Ensures (addNewKeypair pid newKey) (fun s => s.wg.device = some d)
      (fun _ s => ∃ final, s.wg.device = some final ∧
        RotationRun pid d (rotationPlan p k.iAmTheInitiator newKey) final ∧
        final.peers[pid]? = some (rotationPeer (rotationPlan p k.iAmTheInitiator newKey) p)) := by
  intro w ambient result final after pre run
  obtain ⟨out, device, effect⟩ := addNewKeypair_effect pid newKey d p k resident key w ambient result final after pre run
  exact ⟨out, device, effect, rotationRun_peer effect p resident⟩

theorem rotation_ready_returns (pid : PeerId) (newKey : KeypairId)
    (d : Device) (p : Peer) (k : Keypair)
    (resident : d.peers[pid]? = some p) (key : d.keypairs[newKey]? = some k)
    (ready : ClearReady d (rotationReleases (rotationPlan p k.iAmTheInitiator newKey))) :
    Campaign2.Returns (addNewKeypair pid newKey) (fun s => s.wg.device = some d)
      (fun _ s => ∃ final, s.wg.device = some final ∧
        RotationRun pid d (rotationPlan p k.iAmTheInitiator newKey) final ∧
        final.peers[pid]? = some (rotationPeer (rotationPlan p k.iAmTheInitiator newKey) p)) := by
  intro w ambient pre
  obtain ⟨result, final, after, run, post⟩ := addNewKeypair_returns_ready pid newKey d p k resident key ready w ambient pre
  exact ⟨result, final, after, run, rotation_ordered pid newKey d p k resident key w ambient result final after pre run⟩

theorem confirmation_ordered (pid : PeerId) (received : KeypairId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (receivedWithKeypair pid received) (fun s => s.wg.device = some d)
      (fun ok s => ∃ final, s.wg.device = some final ∧ ConfirmationEffect pid received d p ok final ∧
        final.peers[pid]? = some (if ok then rotationPeer (confirmationPlan p received) p else p)) := by
  intro w ambient ok final after pre run
  obtain ⟨out, device, effect⟩ := receivedWithKeypair_effect pid received d p resident w ambient ok final after pre run
  exact ⟨out, device, effect, confirmationEffect_peer pid received d out p ok resident effect⟩

theorem confirmation_ready_returns (pid : PeerId) (received : KeypairId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (ready : p.keypairNext = some received → ClearReady d [p.keypairPrevious]) :
    Campaign2.Returns (receivedWithKeypair pid received) (fun s => s.wg.device = some d)
      (fun ok s => ∃ final, s.wg.device = some final ∧ ConfirmationEffect pid received d p ok final ∧
        final.peers[pid]? = some (if ok then rotationPeer (confirmationPlan p received) p else p)) := by
  intro w ambient pre
  obtain ⟨ok, final, after, run, post⟩ := receivedWithKeypair_returns_ready pid received d p resident ready w ambient pre
  exact ⟨ok, final, after, run, confirmation_ordered pid received d p resident w ambient ok final after pre run⟩

end Leanux.Proofs.WG.Noise
