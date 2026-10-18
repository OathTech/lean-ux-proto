import Leanux.Proofs.WG.Index.ExpiryIndexEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Queues.RxCredits

/-- Original normal expiry retains coverage and retirement. Residency, valid
clock records and optional-key presence are derived where needed from the actual
normal call. Missing device/peer/key, NULL embedded handshake owner, and record
failures retain their original Stops; absent optional key slots are skipped. -/
theorem expireCurrentPeerKeypairs_hashSlots_retirement (retired : Reservations) (pid : PeerId) :
    Campaign2.Ensures (expireCurrentPeerKeypairs pid)
      (fun s => View.HashSlotsSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.HashSlotsSafe s ∧ View.RetirementSafe retired s) := by
  intro g ambient result out after pre run
  cases device : g.dev with
  | none =>
    simp [expireCurrentPeerKeypairs,requireNotPending,handshakeClear,
      IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
      device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [expireCurrentPeerKeypairs,requireNotPending,handshakeClear,
        IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
        device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨now,finalDevice⟩ := Config.expireCurrent_exact pid d p resident
        g ambient result out after device run
      have kept := expiredDevice_hashSlots_retirement retired d pid p now resident
        (pre.1 d device) (pre.2 d device)
      constructor
      · intro actual found
        change out.dev=some actual at found
        rw [finalDevice] at found
        cases found
        exact kept.1
      · intro actual found
        change out.dev=some actual at found
        rw [finalDevice] at found
        cases found
        exact kept.2

/-- The full local index package survives original expiry. No initialized
reachability, successful-record, live-peer or distinct-slot premise is supplied. -/
theorem expireCurrentPeerKeypairs_indexCore (pid : PeerId) :
    Campaign2.Ensures (expireCurrentPeerKeypairs pid) View.IndexCore
      (fun _ => View.IndexCore) := by
  intro g ambient result out after pre run
  cases device : g.dev with
  | none =>
    simp [expireCurrentPeerKeypairs,requireNotPending,handshakeClear,
      IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
      device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [expireCurrentPeerKeypairs,requireNotPending,handshakeClear,
        IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
        device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨now,finalDevice⟩ := Config.expireCurrent_exact pid d p resident
        g ambient result out after device run
      have initial := pre d device
      have kept := expiredDevice_hashSlots_retirement [] d pid p now resident initial.2.1 initial.2.2.2
      intro actual found
      change out.dev=some actual at found
      rw [finalDevice] at found
      cases found
      exact ⟨expiredDevice_tables d pid p now initial.1,kept.1,
        expiredDevice_owner_coherent d pid p now resident initial.2.2.1,kept.2⟩
end Leanux.Proofs.WG.Index
