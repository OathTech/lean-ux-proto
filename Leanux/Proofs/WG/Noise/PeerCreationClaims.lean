import Leanux.Proofs.WG.Index.OwnerCoherencePeerCreateSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- A normal peer allocation initializes its returned location to zero and
preserves every other optional tag. Numeric refusal preserves all tags. This
also covers cursor overwrite; it does not assert allocation freshness. -/
theorem peerCreate_tag_map (publicKey : Key) (psk : Option Key)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (peerCreate publicKey psk) (fun s => s.tagAt = entry.tagAt)
      (fun result after => ∀ target, after.tagAt target = match result with
        | .error _ => entry.tagAt target
        | .ok pid => if pid = target then some HANDSHAKE_ZEROED else entry.tagAt target) := by
  intro g ambient result final after pre run target
  rw [← pre]
  cases device : g.dev with
  | none =>
    simp [peerCreate, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    have effect := Index.peerCreate_owner_fields publicKey psk d
      g ambient result final after device run
    cases result with
    | error code =>
      simp [Campaign2.Snapshot.tagAt, Campaign2.Snapshot.peerAt,
        Campaign2.snapshot, Campaign2.core, device, effect]
    | ok pid =>
      obtain ⟨current, p, present, footprint, resident, _, _, zero⟩ := effect
      by_cases same : pid = target
      · subst target
        simp [Campaign2.Snapshot.tagAt, Campaign2.Snapshot.peerAt,
          Campaign2.snapshot, Campaign2.core, present, resident, zero]
      · simp [Campaign2.Snapshot.tagAt, Campaign2.Snapshot.peerAt,
          Campaign2.snapshot, Campaign2.core, present, device, same,
          footprint.2.2 target (Ne.symm same)]

end Leanux.Proofs.WG.Noise
