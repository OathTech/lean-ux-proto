import Leanux.Proofs.WG.Index.OwnerCoherenceExpiryFrames
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Actual normal handshake clearing preserves every remaining hashed owner's
coherence. Missing peers and NULL embedded words retain their stopped paths. -/
theorem handshakeClear_owner_coherent (pid : PeerId) :
    Campaign2.Ensures (handshakeClear pid) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) := by
  intro g ambient result out after pre run
  cases device : g.dev with
  | none =>
    simp [handshakeClear, IndexOwner.peerDeref, IndexOwner.peerWord, getPeer, getDev,
      device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [handshakeClear, IndexOwner.peerDeref, IndexOwner.peerWord, getPeer, getDev,
        device, resident, invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      have exactClear : Ensures (handshakeClear pid) (fun g => g.dev = some d)
          (fun _ g => g.dev = some (Config.expiryZeroDevice d pid p)) := by
        simpa only [Config.expiryReadPrefix, requireNotPending, pure_bind] using
          Config.expiryReadPrefix_exact pid d p resident
      have finalDevice := exactClear g ambient result out after device run
      intro observed present
      change out.dev = some observed at present
      rw [finalDevice] at present
      cases present
      exact expiryZeroDevice_owner_coherent d pid p resident (pre d device)

/-- Actual normal expiry preserves hashed-owner coherence without reference,
clock-readiness, slot residency or distinctness assumptions. The clock and
missing optional-key failures remain in the source's partial domain. -/
theorem expireCurrentPeerKeypairs_owner_coherent (pid : PeerId) :
    Campaign2.Ensures (expireCurrentPeerKeypairs pid) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) := by
  intro g ambient result out after pre run
  cases device : g.dev with
  | none =>
    simp [expireCurrentPeerKeypairs, requireNotPending, handshakeClear,
      IndexOwner.peerDeref, IndexOwner.peerWord, getPeer, getDev,
      device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [expireCurrentPeerKeypairs, requireNotPending, handshakeClear,
        IndexOwner.peerDeref, IndexOwner.peerWord, getPeer, getDev,
        device, resident, invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨now,finalDevice⟩ := Config.expireCurrent_exact pid d p resident
        g ambient result out after device run
      intro observed present
      change out.dev = some observed at present
      rw [finalDevice] at present
      cases present
      exact expiredDevice_owner_coherent d pid p now resident (pre d device)

end Leanux.Proofs.WG.Index
