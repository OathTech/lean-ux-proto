import Leanux.Proofs.WG.Noise.ConfirmationSequenceSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

theorem confirmation_sequence (pid : PeerId) (ids : List KeypairId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (ids.mapM (receivedWithKeypair pid)) (fun s => s.wg.device = some d)
      (fun results s => ∃ final, s.wg.device = some final ∧
        ConfirmationSequenceEffect pid ids d p results final ∧
        results.length = ids.length ∧ results.count true ≤ 1) := by
  intro w ambient results out after pre run
  obtain ⟨final, device, effect⟩ :=
    confirmationSequence_effect pid ids d p resident w ambient results out after pre run
  exact ⟨final, device, effect,
    confirmationSequenceEffect_length pid ids d final p results effect,
    confirmationSequenceEffect_count pid ids d final p results effect⟩

theorem confirmation_sequence_ready_returns (pid : PeerId) (ids : List KeypairId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (ready : (∃ id ∈ ids, p.keypairNext = some id) → ClearReady d [p.keypairPrevious]) :
    Campaign2.Returns (ids.mapM (receivedWithKeypair pid)) (fun s => s.wg.device = some d)
      (fun results s => ∃ final, s.wg.device = some final ∧
        ConfirmationSequenceEffect pid ids d p results final ∧
        results.length = ids.length ∧ results.count true ≤ 1) := by
  intro w ambient pre
  obtain ⟨results, out, after, run, final, device, effect⟩ :=
    confirmationSequence_returns_ready pid ids d p resident ready w ambient pre
  exact ⟨results, out, after, run, final, device, effect,
    confirmationSequenceEffect_length pid ids d final p results effect,
    confirmationSequenceEffect_count pid ids d final p results effect⟩

end Leanux.Proofs.WG.Noise
