import Leanux.Proofs.WG.Noise.ClearSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Existing ordered-clear claims over the native campaign projection. Their
postconditions observe the Device and ordered release relation; they impose
no exact fixture-snapshot equality or product-callback restriction. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

theorem clear_ordered (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (keypairsClear pid) (fun s => s.wg.device = some d)
      (fun _ s => ∃ final, s.wg.device = some final ∧
        ClearRun pid d [.next, .previous, .current] final ∧
        final.peers[pid]? = some { p with
          keypairNext := none, keypairPrevious := none, keypairCurrent := none }) := by
  intro g ambient result final after pre run
  change g.dev = some d at pre
  obtain ⟨out, device, effect⟩ :=
    keypairsClear_effect pid d p resident g ambient result final after pre run
  have peer := keypairsClear_peer pid p g ambient result final after
    (by simp [peerAt, pre, resident]) run
  exact ⟨out, device, effect, by simpa [peerAt, device] using peer⟩

theorem clear_ready_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (ready : ClearReady d (clearKeys p)) :
    Campaign2.Returns (keypairsClear pid) (fun s => s.wg.device = some d)
      (fun _ s => ∃ final, s.wg.device = some final ∧
        ClearRun pid d [.next, .previous, .current] final ∧
        final.peers[pid]? = some { p with
          keypairNext := none, keypairPrevious := none, keypairCurrent := none }) := by
  intro g ambient pre
  obtain ⟨result, final, after, run, effect⟩ :=
    keypairsClear_returns_ready pid d p resident ready g ambient pre
  exact ⟨result, final, after, run,
    clear_ordered pid d p resident g ambient result final after pre run⟩

end Leanux.Proofs.WG.Noise
