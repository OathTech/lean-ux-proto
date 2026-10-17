import Leanux.Proofs.WG.Index.OwnerCoherenceFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceHeldFrames
import Leanux.Proofs.WG.Config.QueuedReferenceSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Held-reference variant of `Keypairs/Frames/WGBase.peerGet_spec`.
The actual acquisition derives the held reference needed by a later
compensating release. This strengthens the shared peer-get frame with its
normal-return effect, without requiring reference readiness at entry. -/
theorem peerGet_spec_ownerHeld_variant (pid : PeerId) :
    Ensures (peerGet pid)
      (fun g => ∀d, g.dev = some d → HashedOwnersCoherent d)
      (fun _ => OwnerPeerHeldWG pid) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [peerGet,requireNotPending,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [peerGet,requireNotPending,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨present,positive⟩ := (ensures_iff _ _ _).mpr
        (Config.peerGet_exact pid d p resident) g ambient result final after device run
      let next := acquirePeer d pid p
      have exactDevice : final.dev = some next := present
      constructor
      · intro actual actualPresent
        rw [exactDevice] at actualPresent
        cases actualPresent
        intro e member
        exact ownerCoherent_acquire d pid p resident e.owner (pre d device e member)
      · exact ⟨next,{p with refcount := p.refcount + 1},exactDevice,
          by simp [next,acquirePeer],by change 1 < p.refcount + 1; omega⟩


end Leanux.Proofs.WG.Index
