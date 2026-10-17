import Leanux.Proofs.WG.Noise.FreshHistoryModel
import Leanux.Proofs.WG.Noise.SessionModel
import Leanux.Proofs.WG.Noise.RotationEffects
import Leanux.Proofs.WG.Index.SessionAllocationFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- The exact session effect determines the next-slot/cursor summary. -/
theorem sessionEffect_freshView (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (ok : Bool) (final : Device) (last : Nat)
    (resident : d.peers[pid]? = some p)
    (effect : SessionEffect pid d p counter ok final last) :
    FreshViewStep (freshInstallView pid (some d)) none (freshInstallView pid (some final)) := by
  cases ok with
  | false =>
    obtain ⟨rfl,_⟩ := effect
    exact .same _
  | true =>
    obtain ⟨_,_,_,_,birth,rotated,steps,_,rfl⟩ := effect
    have cursor := Index.rotationRun_allocation_cursor steps
    have peer := rotationRun_peer steps (sessionZeroPeer p) (by simp [sessionPrepared])
    have plan : (rotationPeer (rotationPlan (sessionZeroPeer p)
        (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId)
        (sessionZeroPeer p)).keypairNext =
        if p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE then none else some d.nextKeypairId := by
      by_cases role : p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE <;>
        cases next : p.keypairNext <;>
        simp [rotationPlan,rotateWithNext,rotateWithoutNext,rotateResponder,
          rotationPeer,RotationWrite.apply,sessionZeroPeer,role,next]
    have cursorEq : rotated.nextKeypairId = d.nextKeypairId+1 := by
      simpa [sessionPrepared,sessionDerivedDevice,Index.createdDevice] using cursor
    simp only [freshInstallView,Option.map_some,Option.bind_some,resident,peer,Option.map_some,plan,cursorEq]
    exact .allocate d.nextKeypairId (some p.keypairNext)
      (if p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE then none else some d.nextKeypairId)
      (by split <;> simp)

/-- Matching confirmation clears next; the release leaves the allocation cursor
unchanged even when old slots alias. Mismatch preserves the actual Device. -/
theorem confirmationEffect_freshView (pid id : Nat) (d : Device) (p : Peer)
    (ok : Bool) (final : Device) (resident : d.peers[pid]? = some p)
    (effect : ConfirmationEffect pid id d p ok final) :
    FreshViewStep (freshInstallView pid (some d)) (if ok then some id else none)
      (freshInstallView pid (some final)) := by
  by_cases matched : p.keypairNext = some id
  · simp only [ConfirmationEffect,matched,ite_true] at effect
    obtain ⟨rfl,steps⟩ := effect
    have cursor := Index.rotationRun_allocation_cursor steps
    have peer := rotationRun_peer steps p resident
    simpa [freshInstallView,resident,peer,rotationPeer,confirmationPlan,RotationWrite.apply,matched,cursor]
      using FreshViewStep.confirm d.nextKeypairId id
  · simp only [ConfirmationEffect,matched,ite_false] at effect
    obtain ⟨rfl,rfl⟩ := effect
    exact .same _

theorem freshSeen_initial (pid : PeerId) (entry : Campaign2.Snapshot)
    (bound : FreshNextBound pid entry) : FreshSeen (freshInstallView pid entry.wg.device) [] := by
  refine ⟨by simp,by simp,by simp,?_⟩
  intro cursor id hasCursor hasNext
  cases device : entry.wg.device with
  | none => simp [freshInstallView,device] at hasCursor
  | some d =>
    have cursorEq : d.nextKeypairId = cursor := by simpa [freshInstallView,device] using hasCursor
    cases resident : d.peers[pid]? with
    | none => simp [freshInstallView,device,resident] at hasNext
    | some p =>
      have pending : p.keypairNext = some id := by simpa [freshInstallView,device,resident] using hasNext
      rw [← cursorEq]
      exact bound d p id device resident pending

theorem freshSeen_step {before after : Option Nat × Option (Option KeypairId)}
    {confirmed : Option KeypairId} {seen : List KeypairId}
    (step : FreshViewStep before confirmed after) (valid : FreshSeen before seen) :
    FreshSeen after (confirmed.toList ++ seen) := by
  cases step with
  | same view => exact valid
  | allocate cursor beforeNext next role =>
    simp only [Option.toList_none,List.nil_append]
    refine ⟨valid.distinct,?_,?_,?_⟩
    · intro id member current eq
      have old := valid.past id member cursor rfl
      have currentEq : cursor+1 = current := Option.some.inj eq
      rw [← currentEq]
      exact Nat.lt_trans old (Nat.lt_succ_self cursor)
    · intro id member
      have old := valid.past id member cursor rfl
      rcases role with rfl | rfl
      · simp
      · intro equal
        have same : cursor = id := Option.some.inj (Option.some.inj equal)
        exact (Nat.ne_of_lt old) same.symm
    · intro current id eq pending
      have currentEq : cursor+1 = current := Option.some.inj eq
      rcases role with rfl | rfl
      · simp at pending
      · have idEq : cursor = id := Option.some.inj (Option.some.inj pending)
        rw [← currentEq,← idEq]
        exact Nat.lt_succ_self cursor
  | confirm cursor id =>
    simp only [Option.toList_some,List.singleton_append]
    have fresh : id ∉ seen := by
      intro member
      exact valid.away id member rfl
    refine ⟨List.nodup_cons.mpr ⟨fresh,valid.distinct⟩,?_,?_,?_⟩
    · intro other member current eq
      have currentEq : cursor = current := Option.some.inj eq
      subst current
      rcases List.mem_cons.mp member with rfl | member
      · exact valid.next cursor other rfl rfl
      · exact valid.past other member cursor rfl
    · intro other member
      simp
    · intro current other eq pending
      simp at pending


/-- The actual chain transports the finite numeric-ID invariant. -/
theorem FreshChain.preserves {pid : PeerId} {entry final : Campaign2.Snapshot}
    {operations : List FreshOperation} {receipts : List FreshReceipt}
    (chain : FreshChain pid entry operations receipts final) {seen : List KeypairId}
    (valid : FreshSeen (freshInstallView pid entry.wg.device) seen) :
    FreshSeen (freshInstallView pid final.wg.device) (freshConfirmedIds receipts ++ seen) := by
  induction chain generalizing seen with
  | nil => exact valid
  | cons receipt operations receipts final step tail ih =>
    have after := freshSeen_step step valid
    have finish := ih after
    simpa only [freshConfirmedIds,List.append_assoc] using finish


end Leanux.Proofs.WG.Noise
