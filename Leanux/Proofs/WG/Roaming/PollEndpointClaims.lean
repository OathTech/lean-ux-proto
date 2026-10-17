import Leanux.Proofs.WG.Roaming.PollEndpointSource
import Leanux.Proofs.WG.Roaming.PollEndpointFrames
import Leanux.Proofs.WG.Noise.ConsumeEdges

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem packetState_notCrypted (state : PacketState)
    (h : (state != .crypted) = false) : state = .crypted := by
  cases state with
  | crypted => rfl
  | uncrypted => change true = false at h; cases h
  | dead => change true = false at h; cases h

theorem pollEndpointPrefix_facts (pid : PeerId) (entry : Campaign2.Snapshot) :
    Ensures (pollEndpointPrefix pid)
      (fun w => ∀ id, packetAt (Campaign2.snapshot w) id = packetAt entry id)
      (fun result _ => ∀ cut, result = .endpoint cut → PollEndpointFacts pid entry cut) := by
  rw [ensures_iff]
  have hp := fun (q : PrevQueue SkbId) => PrevQueue_peek_spec_wg_variant q
    (fun k => ∀ id, (k.wg.bind fun d => d.rxSkbs[id]?) = packetAt entry id)
  have hg := fun id => getRxSkb_packet id entry
  have hc := fun key nonce => unconstrained_prefix (counterValidate key nonce)
  have he := fun src => endpointFromSkb_exact src (fun _ => True)
  have hs := fun e valid => (ensures_iff _ _ _).mp (setPeerEndpoint_destination pid e valid)
  mvcgen [pollEndpointPrefix, WG.andM, branch, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, invariant, hp, hg, read_get, hc, he, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all (maxSteps := 1000000) [PollEndpointFacts, packetAt, Campaign2.snapshot, Campaign2.core,
    remoteAt, Campaign2.Snapshot.peerAt, destinationAt, sourceEndpoint, Option.bind_map, Function.comp_def]
  all_goals try (split <;> simp_all)
  all_goals grind [packetState_notCrypted]

theorem pollInitialPrefix_facts (pid : PeerId) (budget : Nat) (entry : Campaign2.Snapshot) :
    Ensures (pollInitialPrefix pid budget)
      (fun w => ∀ id, packetAt (Campaign2.snapshot w) id = packetAt entry id)
      (fun result _ => ∀ cut, result = some (.endpoint cut) →
        budget ≠ 0 ∧ PollEndpointFacts pid entry cut) := by
  have hp := (ensures_iff _ _ _).mp (pollEndpointPrefix_facts pid entry)
  rw [ensures_iff]
  mvcgen [pollInitialPrefix, branch, hp]
  all_goals simp_all [packetAt, Campaign2.snapshot, Campaign2.core]

theorem observedRxPoll_facts (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observedRxPoll pid budget toStack) (fun s => s = entry)
      (fun result _ => PollEndpointObservation pid budget entry result) := by
  intro initial result final same run
  subst entry
  change ((rxPoll pid budget toStack).run initial >>= fun out =>
    Except.ok ((out.1, Campaign2.observeResult ((pollInitialPrefix pid budget).run initial)), out.2)) =
      Except.ok (result, final) at run
  cases whole : (rxPoll pid budget toStack).run initial with
  | error e => rw [whole] at run; cases run
  | ok pair =>
    obtain ⟨count, finish⟩ := pair
    rw [whole] at run
    obtain ⟨resultEq, finalEq⟩ := Prod.mk.inj (Except.ok.inj run)
    subst result
    have factored := whole
    rw [rxPoll_first_source, StateT.run_bind] at factored
    cases hpref : (pollInitialPrefix pid budget).run initial with
    | error e => rw [hpref] at factored; cases factored
    | ok pair =>
      obtain ⟨prepared, atCut⟩ := pair
      refine ⟨prepared, Campaign2.snapshot atCut, ?_, ?_⟩
      · simp only [hpref]; rfl
      · exact pollInitialPrefix_facts pid budget (Campaign2.snapshot initial)
          initial prepared atCut (fun _ => rfl) hpref

theorem publication_poll_authentication (pid : PeerId) (pub : PublicationCut)
    (cut : PollEndpointCut) (published : PublishedAuthentication pub)
    (poll : PollEndpointFacts pid pub.publication cut) (same : cut.id = pub.id) :
    PollEndpointAuthentication pub cut := by
  obtain ⟨_, _, _, packet, stored, _, authenticated⟩ := published
  have resident := poll.1
  rw [same, stored] at resident
  have eq : packet = cut.packet := Option.some.inj resident
  subst packet
  exact authenticated poll.2.2.2.1

theorem publicationPollObservation_intro (pid : PeerId) (budget : Nat)
    (pub : PublicationCut) (poll : Nat × Campaign2.Outcome (Option PollPrepared))
    (published : PublishedAuthentication pub)
    (observed : PollEndpointObservation pid budget pub.publication poll) :
    PublicationPollObservation pid budget (true, some (pub, poll)) := by
  refine ⟨rfl, ?_⟩
  intro pub' poll' same
  cases same
  refine ⟨published, observed, ?_⟩
  intro cut atEndpoint present selected
  obtain ⟨prepared, atCut, actual, facts⟩ := observed
  rw [present] at actual
  obtain ⟨preparedEq, _⟩ := Prod.mk.inj (Except.ok.inj actual)
  subst prepared
  exact publication_poll_authentication pid pub cut published (facts cut rfl).2 selected

theorem observedDecryptPoll_authenticated (softirq : M Unit) (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) :
    Campaign2.Ensures (observedDecryptPoll softirq pid budget toStack) (fun _ => True)
      (fun result _ => PublicationPollObservation pid budget result) := by
  change Ensures _ _ _
  rw [ensures_iff]
  have hp := (ensures_iff _ _ _).mp (publicationPrefix_authenticated softirq)
  have hr := fun entry => (ensures_iff _ _ _).mp
    (show Ensures (observedRxPoll pid budget toStack)
      (fun w => Campaign2.snapshot w = entry)
      (fun result _ => PollEndpointObservation pid budget entry result) from
        observedRxPoll_facts pid budget toStack entry)
  have hs := unconstrained_prefix softirq
  have hf := fun owner => unconstrained_prefix (peerPut (some owner))
  mvcgen [observedDecryptPoll, hp, hr, hs, hf]
  all_goals try dsimp +zetaDelta only at *
  all_goals first
    | solve | simp_all [PublicationPollObservation]
    | apply publicationPollObservation_intro <;> grind

end Leanux.Proofs.WG.Roaming
