import Leanux.Proofs.WG.Index.RetirementSessionEffects
import Leanux.Proofs.WG.Index.BoundedSessionClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Queues.RxCredits

/-- Normal original-session transport with supplied allocation/rotation
bounds and initial owner coherence. No success or caller-deadness premise. -/
theorem beginSession_retirement (retired : Reservations) (pid : PeerId)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (bounded : KeypairOwnersBounded d) (fresh : SessionRotationFresh p d.nextKeypairId) :
    Campaign2.Ensures (beginSession pid)
      (fun s => s.wg.device = some d ∧ View.OwnerCoherentSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.RetirementSafe retired s) := by
  intro g ambient ok out after pre run
  obtain ⟨final,present,effect⟩ := beginSession_effect pid d p g.keypairCounter
    resident g ambient ok out after ⟨pre.1,rfl⟩ run
  have reserved := sessionEffect_deadHashedReserved retired pid d p
    g.keypairCounter out.keypairCounter ok final resident bounded fresh
      (pre.2.1 d pre.1) (pre.2.2 d pre.1) effect
  intro actual found
  change out.dev = some actual at found
  rw [present] at found
  cases found
  exact reserved

/-- The existing endpoint-bound package supplies the two local freshness
conditions. Retirement is retained by the actual session's normal outcome,
including false refusals; dead finishing sessions keep their original Stop. -/
theorem beginSession_endpoint_retirement (retired : Reservations) (pid : PeerId) :
    Campaign2.Ensures (beginSession pid)
      (fun s => InitializedBounds.EndpointSafe s ∧ View.OwnerCoherentSafe s ∧
        View.RetirementSafe retired s)
      (fun _ s => View.RetirementSafe retired s) := by
  intro g ambient ok out after pre run
  cases device : g.dev with
  | none =>
    simp [beginSession,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    obtain ⟨p,resident⟩ := beginSession_entry_resident pid d g out ambient after ok device run
    have bounds := pre.1 d device
    exact beginSession_retirement retired pid d p resident
      (InitializedBounds.store_hashed_bound d bounds.keys (pre.2.1 d device))
      (InitializedBounds.slots_session_fresh d pid p bounds.slots resident)
      g ambient ok out after ⟨device,pre.2.1,pre.2.2⟩ run
end Leanux.Proofs.WG.Index
