import Leanux.Proofs.WG.Index.HashSlotModel
import Leanux.Proofs.WG.Index.OwnerCoherenceSlotRemovalFrames
import Leanux.Proofs.WG.Index.SessionCoherenceFrames
import Leanux.Proofs.WG.Noise.RotationClaims
import Leanux.Proofs.WG.Noise.SessionSource
import Leanux.Proofs.WG.Index.SessionInvariantEffects
import Leanux.Proofs.WG.Index.SessionSequenceSource

import Leanux.Proofs.WG.Index.HashSlotSessionEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

theorem beginSession_hashSlots (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (bounded : KeypairOwnersBounded d)
    (fresh : SessionRotationFresh p d.nextKeypairId) :
    Campaign2.Ensures (beginSession pid)
      (fun s => s.wg.device = some d ∧ View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s)
      (fun _ s => View.HashSlotsSafe s) := by
  intro g ambient ok out after pre run
  obtain ⟨final,present,effect⟩ := beginSession_effect pid d p g.keypairCounter
    resident g ambient ok out after ⟨pre.1,rfl⟩ run
  have covered := sessionEffect_hashSlotCoverage pid d p g.keypairCounter out.keypairCounter
    ok final resident bounded fresh (pre.2.1 d pre.1) (pre.2.2 d pre.1) effect
  intro actual found
  change out.dev = some actual at found
  rw [present] at found
  cases found
  exact covered

/-- The established session invariant derives allocation bounds and rotation freshness at the actual entry. This is normal-return transport, not an initialized-driver closure or totality claim. -/
theorem beginSession_sessionHashSlots (pid : PeerId) :
    Campaign2.Ensures (beginSession pid)
      (fun s => View.SessionIndexSafe s ∧ View.HashSlotsSafe s)
      (fun _ s => View.HashSlotsSafe s) := by
  intro g ambient ok out after pre run
  cases device : g.dev with
  | none =>
    simp [beginSession,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    obtain ⟨p,resident⟩ := beginSession_entry_resident pid d g out ambient after ok device run
    have initial := pre.1 d device
    exact beginSession_hashSlots pid d p resident
      (affiliation_hashed_bound d initial.affiliation initial.coherent)
      (affiliation_session_fresh d pid p initial.affiliation resident)
      g ambient ok out after ⟨device,(fun actual found => (pre.1 actual found).coherent),pre.2⟩ run

end Leanux.Proofs.WG.Index
