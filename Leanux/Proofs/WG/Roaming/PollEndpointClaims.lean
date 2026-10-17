import Leanux.Proofs.WG.Roaming.PollEndpointSource
import Leanux.Proofs.WG.Roaming.PollEndpointFrames
import Leanux.Proofs.WG.Roaming.EndpointClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

theorem packetState_notCrypted (state : PacketState)
    (h : (state != .crypted) = false) : state = .crypted := by
  cases state with
  | crypted => rfl
  | uncrypted => change true = false at h; cases h
  | dead => change true = false at h; cases h

theorem pollEndpointPrefix_facts (pid : PeerId) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (pollEndpointPrefix pid)
      (fun s => ∀ id, packetAt s id = packetAt entry id)
      (fun result _ => ∀ cut, result = .endpoint cut → PollEndpointFacts pid entry cut) := by
  let K : WGWorld → Prop := fun g => ∀ id, (g.dev.bind fun d => d.rxSkbs[id]?) = packetAt entry id
  let R : PollPrepared → World → Prop := fun result _ =>
    ∀ cut, result = .endpoint cut → PollEndpointFacts pid entry cut
  have hlift {α : Type} (a : WG.M α) (P : WGWorld → Prop)
      (Q : α → WGWorld → Prop) (h : Ensures a P Q) :
      Noise.Product.Ensures (liftWG a) (fun w => P w.wg) (fun x w => Q x w.wg) := by
    intro w x final pre run
    change ((a.run w.wg).run w.ambient >>= fun ((v, g), ambient) =>
      Except.ok (v, {w with wg := g, ambient})) = _ at run
    cases native : (a.run w.wg).run w.ambient with
    | error e => rw [native] at run; cases run
    | ok out =>
      rcases out with ⟨⟨v, g⟩, ambient⟩
      rw [native] at run
      cases run
      exact h w.wg w.ambient x g ambient pre native
  have hany {α : Type} (a : Leanux.M α) :
      Noise.Product.Ensures a (fun _ => True) (fun _ _ => True) := by
    intro _ _ _ _ _
    trivial
  have hbranch {α : Type} (site : Decision) (value : Bool)
      (f : Bool → Leanux.M α) (Q : α → World → Prop)
      (h : Noise.Product.Ensures (f value) (fun _ => True) Q) :
      Noise.Product.Ensures ((branch site value : Leanux.M Bool) >>= f) (fun _ => True) Q := by
    intro w x final pre run
    let next := {w with ambient := {w.ambient with steps := w.ambient.steps.push {
      decision := site, outcome := value, netRx := w.ambient.netRxSection}}}
    exact h next x final pre run
  have hreject (id : SkbId) (p : RxPacket) :
      Noise.Product.Ensures (pure (.rejected id p) : Leanux.M PollPrepared) (fun _ => True) R := by
    intro w result final pre run cut same
    cases run
    cases same
  have hstop (message : String) :
      Noise.Product.Ensures (invariant message : Leanux.M PollPrepared) (fun _ => True) R := by
    intro w result final pre run
    cases run
  let tail (id : SkbId) (pkt : RxPacket) (beforeRead : Campaign2.Product.Snapshot) : Leanux.M PollPrepared := do
    if pkt.peer != pid then invariant "a packet on another peer's rx_queue"
    setPeer pid { (← getPeer pid) with rxQueue := (← getPeer pid).rxQueue.dropPeeked }
    if ← branch .rxPollNotCrypted (pkt.state != .crypted) then return .rejected id pkt
    let beforeCounter ← Campaign2.Product.read
    let valid ← counterValidate pkt.keypair pkt.nonce
    let afterCounter ← Campaign2.Product.read
    if ← branch .rxPollCounterInvalid !valid then return .rejected id pkt
    let endpoint ← endpointFromSkb pkt.source
    if ← branch .rxPollEndpointFailed endpoint.isNone then return .rejected id pkt
    let some e := endpoint | invariant "unreachable"
    setPeerEndpoint pid e
    let atEndpoint ← Campaign2.Product.read
    return .endpoint ⟨id, pkt, e, beforeRead, beforeCounter, afterCounter,
      .ok (valid, afterCounter), atEndpoint⟩
  have htail (id : SkbId) (pkt : RxPacket) (beforeRead : Campaign2.Product.Snapshot)
      (initial : packetAt entry id = some pkt) (read : packetAt beforeRead id = some pkt) :
      Noise.Product.Ensures (tail id pkt beforeRead) (fun _ => True) R := by
    unfold tail
    by_cases other : (pkt.peer != pid) = true
    · simp only [other, ite_true]
      exact hstop _
    · have peer : pkt.peer = pid := by simpa using other
      simp only [other, Bool.false_eq_true, ite_false]
      refine Noise.Product.ensures_bind _ _ (hany (liftWG (getPeer pid))) ?_
      intro p
      refine Noise.Product.ensures_bind _ _ (hany (liftWG (getPeer pid))) ?_
      intro p2
      refine Noise.Product.ensures_bind _ _ (hany (liftWG (setPeer pid _))) ?_
      intro _
      refine hbranch _ _ _ _ ?_
      cases crypted : (pkt.state != .crypted) with
      | true => exact hreject id pkt
      | false =>
        have state := packetState_notCrypted pkt.state crypted
        simp only [Bool.false_eq_true, ite_false]
        refine Noise.Product.ensures_bind _ _ (hany Campaign2.Product.read) ?_
        intro beforeCounter
        refine Noise.Product.ensures_bind _ _ (hany (liftWG (counterValidate pkt.keypair pkt.nonce))) ?_
        intro valid
        refine Noise.Product.ensures_bind _ _ (hany Campaign2.Product.read) ?_
        intro afterCounter
        refine hbranch _ _ _ _ ?_
        cases valid with
        | false => exact hreject id pkt
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          refine Noise.Product.ensures_bind _ _
            (hlift _ (fun _ => True) _ ((ensures_iff _ _ _).mpr (endpointFromSkb_exact pkt.source (fun _ => True)))) ?_
          intro endpoint w result final pre run
          obtain ⟨_, rfl, family⟩ := pre
          have valid : (sourceEndpoint pkt.source).family = AF_INET ∨
              (sourceEndpoint pkt.source).family = AF_INET6 := by
            rcases family with v4 | v6
            · exact Or.inl (by simp [sourceEndpoint, v4])
            · exact Or.inr (by simp [sourceEndpoint, v6])
          have finish : Noise.Product.Ensures (do
              setPeerEndpoint pid (sourceEndpoint pkt.source)
              let atEndpoint ← Campaign2.Product.read
              pure (PollPrepared.endpoint ⟨id, pkt, sourceEndpoint pkt.source, beforeRead, beforeCounter,
                afterCounter, .ok (true, afterCounter), atEndpoint⟩))
              (fun _ => True) R := by
            refine Noise.Product.ensures_bind _ _
              (hlift _ (fun _ => True) _ (setPeerEndpoint_destination pid _ valid)) ?_
            intro _ w result final pre run cut same
            change Except.ok (PollPrepared.endpoint ⟨id, pkt, sourceEndpoint pkt.source, beforeRead, beforeCounter,
              afterCounter, .ok (true, afterCounter), Campaign2.Product.snapshot w⟩, w) = _ at run
            cases run
            cases same
            exact ⟨initial, read, peer, state, rfl, rfl, family, pre⟩
          exact (hbranch .rxPollEndpointFailed false _ R finish) w result final trivial run
  have hreadPeer : Ensures (getPeer pid) K (fun _ => K) := by
    intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid K) g ambient p final after pre run).1
  have hsetPeer (p : Peer) : Ensures (setPeer pid p) K (fun _ => K) := by
    intro g ambient result final after pre run
    change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
      {d with peers := d.peers.insert pid p})}), ambient) = _ at run
    cases run
    simpa [K, Option.bind_map, Function.comp_def] using pre
  have hgo (first : Option SkbId) : Ensures (WG.andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted)) K (fun _ => K) := by
    intro g ambient result final after pre run
    cases first with
    | none =>
      simp [WG.andM, branch, AmbientM.branch] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
    | some id =>
      cases device : g.dev with
      | none =>
        simp [WG.andM, branch, AmbientM.branch, getRxSkb, liftSkb, getDev, device,
          invariant, AmbientM.invariant] at run
        cases run
      | some d =>
        cases stored : d.rxSkbs[id]? with
        | none =>
          simp [WG.andM, branch, AmbientM.branch, getRxSkb, liftSkb, getDev, device,
            SkbStore.getRx, stored, invariant, AmbientM.invariant] at run
          cases run
        | some p =>
          simp [WG.andM, branch, AmbientM.branch, getRxSkb, liftSkb, getDev, device,
            SkbStore.getRx, stored, modifyDev] at run
          rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
          simpa [K, device] using pre
  change Noise.Product.Ensures (pollEndpointPrefix pid) (fun w => K w.wg) R
  unfold pollEndpointPrefix
  refine Noise.Product.ensures_bind _ _ (hlift _ K _ hreadPeer) ?_
  intro p
  refine Noise.Product.ensures_bind _ _
    (hlift _ K _ ((ensures_iff _ _ _).mpr (PrevQueue_peek_spec_wg_variant p.rxQueue K))) ?_
  intro peek
  obtain ⟨first, q⟩ := peek
  refine Noise.Product.ensures_bind _ _ (hlift _ K _ hreadPeer) ?_
  intro p
  refine Noise.Product.ensures_bind _ _ (hlift _ K _ (hsetPeer _)) ?_
  intro _
  refine Noise.Product.ensures_bind _ _ (hlift _ K _ (hgo first)) ?_
  intro go
  cases go with
  | false =>
    intro w result final pre run cut same
    cases run
    cases same
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    cases first with
    | none =>
      intro w result final pre run
      cases run
    | some id =>
      refine Noise.Product.ensures_bind _ _
        ((Noise.Product.ensures_iff _ _ _).mpr
          (read_snapshot (fun w : World => K w.wg) Campaign2.Product.snapshot)) ?_
      intro beforeRead w result final pre run
      obtain ⟨rfl, property⟩ := pre
      change ((liftWG (getRxSkb id)).run w >>= fun (pkt, next) =>
        (tail id pkt (Campaign2.Product.snapshot w)).run next) = _ at run
      cases hr : (liftWG (getRxSkb id)).run w with
      | error e => rw [hr] at run; cases run
      | ok out =>
        obtain ⟨pkt, next⟩ := out
        obtain ⟨same, read⟩ := getRxSkb_read id w w pkt next rfl hr
        subst next
        rw [hr] at run
        exact htail id pkt (Campaign2.Product.snapshot w) ((property id).symm.trans read) read
          w result final trivial run

theorem pollInitialPrefix_facts (pid : PeerId) (budget : Nat) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (pollInitialPrefix pid budget)
      (fun s => ∀ id, packetAt s id = packetAt entry id)
      (fun result _ => ∀ cut, result = some (.endpoint cut) →
        budget ≠ 0 ∧ PollEndpointFacts pid entry cut) := by
  intro w result final pre run cut same
  by_cases zero : budget = 0
  · simp [pollInitialPrefix, branch, AmbientM.branch, zero] at run
    rcases run with ⟨rfl, rfl⟩
    cases same
  · let next := {w with ambient := {w.ambient with steps := w.ambient.steps.push {
      decision := .rxPollNoBudget, outcome := false, netRx := w.ambient.netRxSection}}}
    have falseB : (budget == 0) = false := by simp [zero]
    change (((branch .rxPollNoBudget (budget == 0) : Leanux.M Bool).run w) >>= fun (b, after) =>
      ((if b then pure none else do
        let prepared ← pollEndpointPrefix pid
        pure (some prepared)) : Leanux.M (Option PollPrepared)).run after) = _ at run
    have tested : (branch .rxPollNoBudget (budget == 0) : Leanux.M Bool).run w =
        .ok (false, next) := by simp [branch, AmbientM.branch, falseB, next]; rfl
    rw [tested] at run
    change ((pollEndpointPrefix pid).run next >>= fun (prepared, out) =>
      Except.ok (some prepared, out)) = _ at run
    cases prefixRun : (pollEndpointPrefix pid).run next with
    | error e => rw [prefixRun] at run; cases run
    | ok pair =>
      obtain ⟨prepared, out⟩ := pair
      rw [prefixRun] at run
      cases run
      exact ⟨zero, pollEndpointPrefix_facts pid entry next prepared final pre prefixRun cut
        (Option.some.inj same)⟩

theorem observedRxPoll_facts (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (observedRxPoll pid budget toStack) (fun s => s = entry)
      (fun result _ => PollEndpointObservation pid budget entry result) := by
  intro initial result final same run
  subst entry
  change ((rxPoll pid budget toStack).run initial >>= fun out =>
    Except.ok ((out.1, Campaign2.Product.observeResult ((pollInitialPrefix pid budget).run initial)), out.2)) =
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
      refine ⟨prepared, Campaign2.Product.snapshot atCut, ?_, ?_⟩
      · rfl
      · exact pollInitialPrefix_facts pid budget (Campaign2.Product.snapshot initial)
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
    (pub : PublicationCut) (poll : Nat × Campaign2.Product.Outcome (Option PollPrepared))
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

theorem observedDecryptPoll_authenticated (softirq : Leanux.M Unit) (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) :
    Campaign2.Product.Ensures (observedDecryptPoll softirq pid budget toStack) (fun _ => True)
      (fun result _ => PublicationPollObservation pid budget result) := by
  have preserve {α : Type} (a : Leanux.M α) (P : Prop) :
      Noise.Product.Ensures a (fun _ => P) (fun _ _ => P) := by
    intro w result final pre run
    exact pre
  change Noise.Product.Ensures _ _ _
  unfold observedDecryptPoll
  refine Noise.Product.ensures_bind _ _ (publicationPrefix_authenticated softirq) ?_
  intro publication
  cases publication with
  | none =>
    intro w result final pre run
    cases run
    exact ⟨rfl, by intro pub poll impossible; cases impossible⟩
  | some pub =>
    have hpoll : Noise.Product.Ensures (observedRxPoll pid budget toStack)
        (fun w => ∀ cut, some pub = some cut →
          cut.publication = Campaign2.Product.snapshot w ∧ PublishedAuthentication cut)
        (fun poll _ => PublicationPollObservation pid budget (true, some (pub, poll))) := by
      intro w result final pre run
      obtain ⟨same, published⟩ := pre pub rfl
      exact publicationPollObservation_intro pid budget pub result published
        (observedRxPoll_facts pid budget toStack pub.publication w result final same.symm run)
    refine Noise.Product.ensures_bind _ _ hpoll ?_
    intro poll
    refine Noise.Product.ensures_bind _ _
      (preserve (liftWG (peerPut (some pub.owner))) _) ?_
    intro _
    refine Noise.Product.ensures_bind _ _ (preserve softirq _) ?_
    intro _ w result final pre run
    cases run
    exact pre

end Leanux.Proofs.WG.Roaming
