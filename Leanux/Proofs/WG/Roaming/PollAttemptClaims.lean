import Leanux.Proofs.WG.Roaming.PollAttemptAuditSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Campaign2 Std.Do

theorem pollAttemptPrefix_facts (pid : PeerId) (entry : Campaign2.Snapshot) :
    Ensures (pollAttemptPrefix pid)
      (fun w => ∀ id, packetAt (Campaign2.snapshot w) id = packetAt entry id)
      (fun result w => ∀ cut, result = .endpoint cut →
        cut.beforeSetter = snapshot w ∧ PollAttemptFacts pid entry cut) := by
  rw [ensures_iff]
  have hp := fun (q : PrevQueue SkbId) => PrevQueue_peek_spec_wg_variant q
    (fun k => ∀ id, (k.wg.bind fun d => d.rxSkbs[id]?) = packetAt entry id)
  have hg := fun id => getRxSkb_packet id entry
  have hc := fun key nonce => unconstrained_prefix (counterValidate key nonce)
  have he := fun src => endpointFromSkb_exact src (fun _ => True)
  mvcgen [pollAttemptPrefix, WG.andM, branch, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, invariant, hp, hg, read_get, hc, he]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all (maxSteps := 1000000) [PollAttemptFacts, packetAt, Campaign2.snapshot, Campaign2.core,
    remoteAt, Campaign2.Snapshot.peerAt, destinationAt, sourceEndpoint, Option.bind_map, Function.comp_def]
  all_goals try (split <;> simp_all)
  all_goals grind [packetState_notCrypted]

theorem pollAttemptStepRun_facts (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (state : PollState) (entry : World) :
    PollAttemptIterationFacts pid (pollAttemptStepRun pid budget toStack state entry).1 := by
  unfold pollAttemptStepRun
  cases h : (pollAttemptPrefix pid).run entry with
  | error error => simp [PollAttemptIterationFacts]
  | ok pair =>
    obtain ⟨prepared, before⟩ := pair
    have facts := pollAttemptPrefix_facts pid (snapshot entry) entry prepared before
      (fun _ => rfl) h
    refine ⟨?_, ?_, ?_⟩
    · intro error impossible
      cases impossible
    · intro value atCut same
      rfl
    · intro cut atCut same
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
      exact facts cut rfl

theorem pollAttemptLoopRun_facts (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (turns : List Nat) (state : PollState) (entry : World) :
    ∀ iteration ∈ (pollAttemptLoopRun pid budget toStack turns state entry).1,
      PollAttemptIterationFacts pid iteration := by
  induction turns generalizing state entry with
  | nil => simp [pollAttemptLoopRun]
  | cons turn turns ih =>
    have head := pollAttemptStepRun_facts pid budget toStack state entry
    simp only [pollAttemptLoopRun]
    cases h : (pollAttemptStepRun pid budget toStack state entry).2 with
    | error error => simpa using head
    | ok pair =>
      obtain ⟨step, out⟩ := pair
      cases step with
      | done next => simpa using head
      | yield next =>
        intro iteration member
        rcases List.mem_cons.mp member with rfl | member
        · exact head
        · exact ih next out iteration member

theorem pollAttemptAuditRun_facts (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (entry : World) :
    ∀ iteration ∈ (pollAttemptAuditRun pid budget toStack entry).iterations,
      PollAttemptIterationFacts pid iteration := by
  simp only [pollAttemptAuditRun]
  cases h : (branch .rxPollNoBudget (budget == 0)).run entry with
  | error error => simp
  | ok pair =>
    obtain ⟨zero, afterTest⟩ := pair
    cases zero with
    | true => simp
    | false => exact pollAttemptLoopRun_facts pid budget toStack _ _ afterTest

theorem observedPollAttempts_facts (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) :
    Campaign2.Observes (observedPollAttempts pid budget toStack) (fun _ => True)
      (fun entry observed => ∃ audit, observed = .ok (audit, entry) ∧
        ∀ iteration ∈ audit.iterations, PollAttemptIterationFacts pid iteration) := by
  intro entry pre
  exact ⟨pollAttemptAuditRun pid budget toStack entry, rfl,
    pollAttemptAuditRun_facts pid budget toStack entry⟩

end Leanux.Proofs.WG.Roaming
