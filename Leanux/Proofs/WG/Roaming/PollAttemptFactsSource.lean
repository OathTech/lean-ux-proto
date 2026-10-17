import Leanux.Proofs.WG.Roaming.PollAttemptAuditSource
import Leanux.Proofs.WG.Roaming.PollEndpointClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

theorem pollAttemptPrefix_facts (pid : PeerId) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (pollAttemptPrefix pid)
      (fun s => ∀ id, packetAt s id = packetAt entry id)
      (fun result s => ∀ cut, result = .endpoint cut →
        cut.beforeSetter = s ∧ PollAttemptFacts pid entry cut) := by
  let K : WGWorld → Prop := fun g => ∀ id, (g.dev.bind fun d => d.rxSkbs[id]?) = packetAt entry id
  let R : PollAttemptPrepared → World → Prop := fun result w =>
    ∀ cut, result = .endpoint cut →
      cut.beforeSetter = Campaign2.Product.snapshot w ∧ PollAttemptFacts pid entry cut
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
      Noise.Product.Ensures (pure (.rejected id p) : Leanux.M PollAttemptPrepared) (fun _ => True) R := by
    intro w result final pre run cut same
    cases run
    cases same
  have hstop (message : String) :
      Noise.Product.Ensures (invariant message : Leanux.M PollAttemptPrepared) (fun _ => True) R := by
    intro w result final pre run
    cases run
  let tail (id : SkbId) (pkt : RxPacket) (beforeRead : Campaign2.Product.Snapshot) : Leanux.M PollAttemptPrepared := do
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
    let beforeSetter ← Campaign2.Product.read
    return .endpoint ⟨id, pkt, e, beforeRead, beforeCounter, afterCounter,
      .ok (valid, afterCounter), beforeSetter⟩
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
          have finish : Noise.Product.Ensures (do
              let beforeSetter ← Campaign2.Product.read
              pure (PollAttemptPrepared.endpoint ⟨id, pkt, sourceEndpoint pkt.source, beforeRead, beforeCounter,
                afterCounter, .ok (true, afterCounter), beforeSetter⟩))
              (fun _ => True) R := by
            intro w result final pre run cut same
            change Except.ok (PollAttemptPrepared.endpoint ⟨id, pkt, sourceEndpoint pkt.source, beforeRead, beforeCounter,
              afterCounter, .ok (true, afterCounter), Campaign2.Product.snapshot w⟩, w) = _ at run
            cases run
            cases same
            exact ⟨rfl, initial, read, peer, state, rfl, rfl, family⟩
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
  change Noise.Product.Ensures (pollAttemptPrefix pid) (fun w => K w.wg) R
  unfold pollAttemptPrefix
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

/-- Actual product-run support for the projected audit claim. Arbitrary callback
state, including fields outside the Product observation, remains threaded here. -/
theorem pollAttemptStepRun_facts (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (state : PollState) (entry : World) :
    PollAttemptIterationFacts pid (pollAttemptStepRun pid budget toStack state entry).1 := by
  unfold pollAttemptStepRun
  cases h : (pollAttemptPrefix pid).run entry with
  | error error => simp [PollAttemptIterationFacts]
  | ok pair =>
    obtain ⟨prepared, before⟩ := pair
    have facts := pollAttemptPrefix_facts pid (Campaign2.Product.snapshot entry) entry prepared before
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
    (toStack : List (List UInt8) → Leanux.M Unit) (turns : List Nat) (state : PollState) (entry : World) :
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
    (toStack : List (List UInt8) → Leanux.M Unit) (entry : World) :
    ∀ iteration ∈ (pollAttemptAuditRun pid budget toStack entry).iterations,
      PollAttemptIterationFacts pid iteration := by
  simp only [pollAttemptAuditRun]
  cases h : (branch .rxPollNoBudget (budget == 0) : Leanux.M Bool).run entry with
  | error error => simp
  | ok pair =>
    obtain ⟨zero, afterTest⟩ := pair
    cases zero with
    | true => simp
    | false => exact pollAttemptLoopRun_facts pid budget toStack _ _ afterTest

end Leanux.Proofs.WG.Roaming
