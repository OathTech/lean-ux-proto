import Leanux.Proofs.WG.Noise.InterleavedFreshModel
import Leanux.Proofs.WG.Noise.InterleavedFreshFrames
import Leanux.Proofs.WG.Noise.FreshHistoryEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- Actual successful allocation by another peer advances the cursor and leaves
tracked next unchanged. Normal refusal stutters; aliases retain exact effects. -/
theorem sessionEffect_other_freshView (actor tracked : PeerId) (different : actor ≠ tracked)
    (d : Device) (p : Peer) (counter : Nat) (ok : Bool) (final : Device) (last : Nat)
    (effect : SessionEffect actor d p counter ok final last) :
    InterleavedFreshStep (freshInstallView tracked (some d)) none
      (freshInstallView tracked (some final)) := by
  cases ok with
  | false =>
    obtain ⟨rfl,_⟩ := effect
    exact .localStep (.same _)
  | true =>
    obtain ⟨_,_,_,_,birth,rotated,steps,_,rfl⟩ := effect
    have cursor := Index.rotationRun_allocation_cursor steps
    have peer := rotationRun_other_peer different steps
    have cursorEq : rotated.nextKeypairId = d.nextKeypairId+1 := by
      simpa [sessionPrepared,sessionDerivedDevice,Index.createdDevice] using cursor
    have peerEq : rotated.peers[tracked]? = d.peers[tracked]? := by
      simpa [sessionPrepared,sessionDerivedDevice,Index.createdDevice,
        Std.TreeMap.getElem?_insert,different] using peer
    simpa [freshInstallView,cursorEq,peerEq] using
      InterleavedFreshStep.advance d.nextKeypairId ((d.peers[tracked]?).map Peer.keypairNext)

/-- A monotone foreign allocation cannot repeat a tracked confirmation. The
old next-slot bound is transported rather than replaced by a residency premise. -/
theorem interleavedFreshSeen_step {before after : Option Nat × Option (Option KeypairId)}
    {confirmed : Option KeypairId} {seen : List KeypairId}
    (step : InterleavedFreshStep before confirmed after) (valid : FreshSeen before seen) :
    FreshSeen after (confirmed.toList ++ seen) := by
  cases step with
  | localStep step => exact freshSeen_step step valid
  | advance cursor next =>
    simp only [Option.toList_none,List.nil_append]
    refine ⟨valid.distinct,?_,valid.away,?_⟩
    · intro id member current eq
      have old := valid.past id member cursor rfl
      have same : cursor+1 = current := Option.some.inj eq
      rw [← same]
      exact Nat.lt_trans old (Nat.lt_succ_self cursor)
    · intro current id eq pending
      have old := valid.next cursor id rfl pending
      have same : cursor+1 = current := Option.some.inj eq
      rw [← same]
      exact Nat.lt_trans old (Nat.lt_succ_self cursor)

/-- A linked actual history preserves the tracked numeric-ID account through
both local operations and allocations performed for other peers. -/
theorem InterleavedFreshChain.preserves {tracked : PeerId} {entry final : Campaign2.Snapshot}
    {operations : List InterleavedFreshOperation} {receipts : List InterleavedFreshReceipt}
    (chain : InterleavedFreshChain tracked entry operations receipts final) {seen : List KeypairId}
    (valid : FreshSeen (freshInstallView tracked entry.wg.device) seen) :
    FreshSeen (freshInstallView tracked final.wg.device) (interleavedConfirmedIds tracked receipts ++ seen) := by
  induction chain generalizing seen with
  | nil => exact valid
  | cons receipt operations receipts final step tail ih =>
    have after := interleavedFreshSeen_step step valid
    have finish := ih after
    simpa only [interleavedConfirmedIds,List.append_assoc] using finish

end Leanux.Proofs.WG.Noise
