import Leanux.Proofs.WG.Index.InitializedBoundsEffects
import Leanux.Proofs.WG.Index.HashSlotSessionClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceSessionClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- The smaller initialized endpoint bounds suffice for the actual session
coverage/coherence step. Full affiliation is not an entry premise. This
does not assert those bounds or retirement obligations at every driver cut. -/
theorem beginSession_endpoint_hashSlots (pid : PeerId) :
    Campaign2.Ensures (beginSession pid)
      (fun s => InitializedBounds.EndpointSafe s ∧ View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s)
      (fun _ s => View.OwnerCoherentSafe s ∧ View.HashSlotsSafe s) := by
  intro g ambient ok out after pre run
  cases device : g.dev with
  | none =>
    simp [beginSession,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    obtain ⟨p,resident⟩ := beginSession_entry_resident pid d g out ambient after ok device run
    have bounds := pre.1 d device
    have bounded := InitializedBounds.store_hashed_bound d bounds.keys (pre.2.1 d device)
    have fresh := InitializedBounds.slots_session_fresh d pid p bounds.slots resident
    exact ⟨beginSession_owner_coherent pid d p resident bounded fresh
        g ambient ok out after ⟨device,pre.2.1⟩ run,
      beginSession_hashSlots pid d p resident bounded fresh
        g ambient ok out after ⟨device,pre.2.1,pre.2.2⟩ run⟩
end Leanux.Proofs.WG.Index
