import Leanux.Proofs.WG.Roaming.PublicationSource
import Leanux.Proofs.WG.Roaming.Authentication
import Leanux.Proofs.WG.Roaming.PublicationFrames
import Leanux.Proofs.WG.Roaming.PublicationLeafClaims
import Leanux.Proofs.WG.Roaming.PublicationReadFrames
import Leanux.Proofs.WG.Noise.ComponentFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Publishing the selected state preserves the packet's other fields. The
held owner reference and callback-entry snapshot come from the original prefix. -/
theorem enqueuePublication_packet (id : SkbId) (state : PacketState) (P : RxPacket → Prop) :
    Campaign2.Product.Ensures (enqueuePublication id state)
      (fun s => ∀ p, packetAt s id = some p → P p)
      (fun result s => result.2 = s ∧ ∃ p,
        P p ∧ packetAt result.2 id = some { p with state }) := by
  let K : WGWorld → Prop := fun g => ∀ p, (g.dev.bind fun d => d.rxSkbs[id]?) = some p → P p
  let L : WGWorld → Prop := fun g => ∃ p, P p ∧
    (g.dev.bind fun d => d.rxSkbs[id]?) = some {p with state}
  have hlift {α : Type} (a : WG.M α) (S : WGWorld → Prop)
      (Q : α → WGWorld → Prop) (h : Ensures a S Q) :
      Noise.Product.Ensures (liftWG a) (fun w => S w.wg) (fun x w => Q x w.wg) := by
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
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) K (fun _ => K) := by
    intro g ambient x final after pre run
    cases run
    exact pre
  have hkey (key : KeypairId) : Ensures (getKeypair key) K (fun _ => K) := by
    intro g ambient x final after pre run
    cases hd : g.dev with
    | none =>
      simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases hk : d.keypairs[key]? with
      | none =>
        simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at run
        cases run
      | some key =>
        simp [getKeypair, getDev, hd, hk] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        exact pre
  have hderef (key : KeypairId) :
      Ensures (IndexOwner.peerDeref (.keypair key)) K (fun _ => K) := by
    unfold IndexOwner.peerDeref IndexOwner.peerWord
    refine ensures_bind (Q := fun _ => K) _ _ ?_ ?_
    · refine ensures_bind _ _ (hkey key) ?_
      intro k
      exact hpure k.peer
    · intro word
      cases word with
      | none =>
        exact (ensures_iff _ _ _).mpr
          (hoare_liftAmbient_variant (AmbientM.unsupported "entry->peer is NULL: the C dereferences it") K)
      | some pid => exact hpure pid
  have hreadPeer (pid : PeerId) : Ensures (getPeer pid) K (fun _ => K) := by
    intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid K) g ambient p final after pre run).1
  have hsetPeer (Q : Option RxPacket → Prop) (pid : PeerId) (p : Peer) :
      Ensures (setPeer pid p) (fun g => Q (g.dev.bind fun d => d.rxSkbs[id]?))
        (fun _ g => Q (g.dev.bind fun d => d.rxSkbs[id]?)) := by
    intro g ambient x final after pre run
    change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
      {d with peers := d.peers.insert pid p})}), ambient) = _ at run
    cases run
    simpa [Option.bind_map, Function.comp_def] using pre
  have hgetPeer (pid : PeerId) : Ensures (peerGet pid) K (fun _ => K) := by
    unfold peerGet requireNotPending
    simp only [pure_bind]
    refine ensures_bind _ _ (hreadPeer pid) ?_
    intro p
    refine ensures_bind (Q := fun _ => K) _ _ ?_ ?_
    · intro g ambient result final after pre run
      by_cases zero : p.refcount = 0
      · simp [refcountInc, branchCmp, AmbientM.branchCmp, branch, AmbientM.branch,
          unsupported, AmbientM.unsupported, zero] at run
        cases run
      · by_cases overflow : p.refcount + 1 ≥ 2 ^ 31
        · simp [refcountInc, branchCmp, AmbientM.branchCmp, branch, AmbientM.branch,
            unsupported, AmbientM.unsupported, zero, overflow] at run
          cases run
        · simp [refcountInc, branchCmp, AmbientM.branchCmp, branch, AmbientM.branch,
            zero, overflow] at run
          rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
          exact pre
    · intro _
      exact hsetPeer (fun value => ∀ q, value = some q → P q) pid _
  have hreadPacket : Noise.Product.Ensures (liftWG (getRxSkb id))
      (fun w => K w.wg) (fun _ w => K w.wg) := by
    intro w p final pre run
    have same := (getRxSkb_read id w w p final rfl run).1
    simpa [same] using pre
  have hwrite : Noise.Product.Ensures (liftWG (setRxSkb id (fun p => {p with state})))
      (fun w => K w.wg) (fun _ w => L w.wg) := by
    intro w result final pre run
    change (((setRxSkb id (fun p => {p with state})).run w.wg).run w.ambient >>=
      fun ((value, g), ambient) => Except.ok (value, {w with wg := g, ambient})) = _ at run
    cases hd : w.wg.dev with
    | none =>
      simp [setRxSkb, liftSkb, getDev, hd, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases hp : d.rxSkbs[id]? with
      | none =>
        simp [setRxSkb, liftSkb, getDev, hd, SkbStore.setRx, SkbStore.getRx, hp,
          invariant, AmbientM.invariant] at run
        cases run
      | some packet =>
        have property : P packet := pre packet (by simp [hd, hp])
        simp [setRxSkb, liftSkb, getDev, hd, SkbStore.setRx, SkbStore.getRx, hp, modifyDev] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨packet, property, by simp⟩
  change Noise.Product.Ensures (enqueuePublication id state) (fun w => K w.wg)
    (fun result w => result.2 = Campaign2.Product.snapshot w ∧ ∃ p,
      P p ∧ packetAt result.2 id = some {p with state})
  unfold enqueuePublication
  refine Noise.Product.ensures_bind _ _ hreadPacket ?_
  intro packet
  refine Noise.Product.ensures_bind _ _ (hlift _ K _ (hderef packet.keypair)) ?_
  intro pid
  refine Noise.Product.ensures_bind _ _ (hlift _ K _ (hgetPeer pid)) ?_
  intro _
  refine Noise.Product.ensures_bind _ _ (hlift _ K _ (hreadPeer pid)) ?_
  intro p
  by_cases queued : p.rxQueue.all.contains id = true
  · simp only [queued, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine Noise.Product.ensures_bind _ _ hwrite ?_
    intro _
    refine Noise.Product.ensures_bind _ _ (hlift _ L _
      (hsetPeer (fun value => ∃ q, P q ∧ value = some {q with state}) pid _)) ?_
    intro _ w result final pre run
    change Except.ok ((pid, Campaign2.Product.snapshot w), w) = _ at run
    cases run
    exact ⟨rfl, pre⟩
  · simp only [Bool.eq_false_iff.mpr queued, Bool.not_false, ↓reduceIte]
    intro w result final pre run
    change Except.error (Stop.invariant "a decrypted packet that is not on its peer's rx_queue") =
      Except.ok (result, final) at run
    cases run

theorem publicationPublish_packet (id : SkbId) (decrypted : Option RxPacket) :
    Campaign2.Product.Ensures (publicationPublish id decrypted) (fun _ => True)
      (fun result s => result.2 = s ∧ ∃ published,
        packetAt result.2 id = some published ∧
        published.state = (if decrypted.isSome then .crypted else .dead) ∧
        ∀ plain, decrypted = some plain → published = {plain with state := .crypted}) := by
  cases decrypted with
  | none =>
    intro w result final pre run
    let next := {w with ambient := {w.ambient with steps := w.ambient.steps.push {
      decision := .decWorkerDecrypted, outcome := false, netRx := w.ambient.netRxSection}}}
    change (enqueuePublication id .dead).run next = _ at run
    obtain ⟨snap, p, _, stored⟩ := enqueuePublication_packet id .dead (fun _ => True)
      next result final (by intro _ _; trivial) run
    refine ⟨snap, _, stored, rfl, ?_⟩
    intro plain impossible
    cases impossible
  | some plain =>
    have chain : Noise.Product.Ensures (do
        liftWG (setRxSkb id (fun _ => plain))
        enqueuePublication id .crypted) (fun _ => True)
        (fun result w => result.2 = Campaign2.Product.snapshot w ∧ ∃ published,
          packetAt result.2 id = some published ∧ published.state = .crypted ∧
          ∀ p, some plain = some p → published = {p with state := .crypted}) := by
      refine Noise.Product.ensures_bind _ _
        ((Noise.Product.ensures_iff _ _ _).mpr (setRxSkb_plain id plain)) ?_
      intro _ w result final pre run
      obtain ⟨snap, p, same, stored⟩ := enqueuePublication_packet id .crypted (fun p => p = plain)
        w result final (by intro p hp; exact Option.some.inj (hp.symm.trans pre)) run
      subst p
      exact ⟨snap, _, stored, rfl, by intro p same; cases same; rfl⟩
    intro w result final pre run
    let next := {w with ambient := {w.ambient with steps := w.ambient.steps.push {
      decision := .decWorkerDecrypted, outcome := true, netRx := w.ambient.netRxSection}}}
    exact chain next result final pre run

/-- The prefix's successful packet branch has the AEAD provenance at its
publication snapshot. The supplied ring fact is about the actual prior read. -/
theorem publicationPacket_authenticated (after : Campaign2.Product.Snapshot) (id : SkbId)
    (selected : ∃ d ring, after.wg.device = some d ∧
      d.decryptQueue.consume = (some id, ring)) :
    Campaign2.Product.Ensures (publicationPacket after id)
      (fun w => packetAt w id = packetAt after id)
      (fun cut w => cut.id = id ∧ cut.afterSoftirq = after ∧
        cut.publication = w ∧ PublishedAuthentication cut) := by
  intro w cut final same run
  change ((liftWG (getRxSkb id)).run w >>= fun (packet, before) =>
    (liftWG (decryptPacket packet)).run before >>= fun (decrypted, next) =>
      (publicationPublish id decrypted).run next >>= fun (published, finish) =>
        Except.ok (PublicationCut.mk after (Campaign2.Product.snapshot before) id
          published.1 packet decrypted published.2, finish)) = Except.ok (cut, final) at run
  cases hg : (liftWG (getRxSkb id)).run w with
  | error e => rw [hg] at run; cases run
  | ok pair =>
    obtain ⟨pkt, before⟩ := pair
    obtain ⟨unchanged, resident⟩ := getRxSkb_read id w w pkt before rfl hg
    subst before
    rw [hg] at run
    change ((liftWG (decryptPacket pkt)).run w >>= fun dec =>
      (publicationPublish id dec.1).run dec.2 >>= fun pub =>
        Except.ok (PublicationCut.mk after (Campaign2.Product.snapshot w) id pub.1.1 pkt dec.1 pub.1.2, pub.2)) =
      Except.ok (cut, final) at run
    cases hd : (liftWG (decryptPacket pkt)).run w with
    | error e => rw [hd] at run; cases run
    | ok pair =>
      obtain ⟨decrypted, next⟩ := pair
      rw [hd] at run
      change ((publicationPublish id decrypted).run next >>= fun pub =>
        Except.ok (PublicationCut.mk after (Campaign2.Product.snapshot w) id pub.1.1 pkt decrypted pub.1.2, pub.2)) =
        Except.ok (cut, final) at run
      cases hp : (publicationPublish id decrypted).run next with
      | error e => rw [hp] at run; cases run
      | ok pair =>
        obtain ⟨published, finish⟩ := pair
        rw [hp] at run
        change Except.ok (PublicationCut.mk after (Campaign2.Product.snapshot w) id published.1 pkt decrypted published.2,
          finish) = Except.ok (cut, final) at run
        obtain ⟨sameCut, sameFinal⟩ := Prod.mk.inj (Except.ok.inj run)
        subst cut
        subst final
        obtain ⟨snapshot_eq, out, stored, state_eq, plaintext⟩ :=
          publicationPublish_packet id decrypted next published finish trivial hp
        refine ⟨rfl, rfl, snapshot_eq, selected, ?_, resident, out, stored, state_eq, ?_⟩
        · exact same ▸ resident
        · intro crypted
          cases he : decrypted with
          | none => simp [he] at state_eq; simp [state_eq] at crypted
          | some plain =>
            have auth := decryptPacket_authentication_at pkt (Campaign2.Product.snapshot w)
              w decrypted next rfl hd plain he
            obtain ⟨key, keyread, source, peer, keypair, nonce, aead⟩ := auth
            have output := plaintext plain he
            exact ⟨key, keyread, by simpa [output] using source,
              by simpa [output] using peer, by simpa [output] using keypair,
              by simpa [output] using nonce, by simpa [output] using aead⟩

theorem publicationSelected_authenticated (after : Campaign2.Product.Snapshot) (id : SkbId)
    (ring : PtrRing SkbId)
    (selected : ∃ d rest, after.wg.device = some d ∧
      d.decryptQueue.consume = (some id, rest)) :
    Campaign2.Product.Ensures (publicationSelected after id ring)
      (fun s => packetAt s id = packetAt after id)
      (fun cut s => cut.id = id ∧ cut.afterSoftirq = after ∧
        cut.publication = s ∧ PublishedAuthentication cut) := by
  intro w cut final pre run
  let next := {w with
    ambient := {w.ambient with steps := w.ambient.steps.push {
      decision := .decWorkerConsumed, outcome := true, netRx := w.ambient.netRxSection}}
    wg := {w.wg with dev := w.wg.dev.map (fun d : Device => {d with decryptQueue := ring})}}
  change (publicationPacket after id).run next = _ at run
  exact publicationPacket_authenticated after id selected next cut final
    (by simpa [next, packetAt, Campaign2.Product.snapshot, Campaign2.snapshot, Campaign2.core,
      Option.bind_map, Function.comp_def] using pre) run

theorem publicationPrefix_authenticated (softirq : Leanux.M Unit) :
    Campaign2.Product.Ensures (publicationPrefix softirq) (fun _ => True)
      (fun result w => ∀ cut, result = some cut →
        cut.publication = w ∧ PublishedAuthentication cut) := by
  intro initial result final _ run cut same
  simp only [publicationPrefix, StateT.run_bind] at run
  cases hs : softirq.run initial with
  | error e => rw [hs] at run; cases run
  | ok pair =>
    obtain ⟨callbackUnit, after⟩ := pair
    rw [hs] at run
    change ((liftWG getDev).run after >>= fun out =>
      (match out.1.decryptQueue.consume with
       | (none, _) => do
         _ ← branch .decWorkerConsumed false
         pure none
       | (some id, ring) => do
         let c ← publicationSelected (Campaign2.Product.snapshot after) id ring
         pure (some c)).run out.2) = Except.ok (result, final) at run
    cases hdev : after.wg.dev with
    | none =>
      have absent : (liftWG getDev).run after = .error (.invariant "no WireGuard device in this trace's fixture") := by
        change (((getDev.run after.wg).run after.ambient) >>= fun ((d, g), ambient) =>
          Except.ok (d, {after with wg := g, ambient})) = _
        simp [getDev, invariant, AmbientM.invariant, hdev]
        rfl
      rw [absent] at run
      cases run
    | some d =>
      have resident : (liftWG getDev).run after = .ok (d, after) := by
        change (((getDev.run after.wg).run after.ambient) >>= fun ((d, g), ambient) =>
          Except.ok (d, {after with wg := g, ambient})) = _
        simp [getDev, hdev]
      rw [resident] at run
      change (match d.decryptQueue.consume with
        | (none, _) => do
          _ ← branch .decWorkerConsumed false
          pure none
        | (some id, ring) => do
          let c ← publicationSelected (Campaign2.Product.snapshot after) id ring
          pure (some c)).run after = Except.ok (result, final) at run
      cases hc : d.decryptQueue.consume with
      | mk first ring =>
        cases first with
        | none =>
          simp only [hc] at run
          change ((branch .decWorkerConsumed false : Leanux.M Bool).run after >>= fun out =>
            Except.ok (none, out.2)) = Except.ok (result, final) at run
          cases hb : (branch .decWorkerConsumed false : Leanux.M Bool).run after with
          | error e => rw [hb] at run; cases run
          | ok pair =>
            rw [hb] at run
            have impossible : none = result := congrArg Prod.fst (Except.ok.inj run)
            rw [← impossible] at same
            cases same
        | some id =>
          simp only [hc] at run
          change ((publicationSelected (Campaign2.Product.snapshot after) id ring).run after >>= fun out =>
            Except.ok (some out.1, out.2)) = Except.ok (result, final) at run
          cases hp : (publicationSelected (Campaign2.Product.snapshot after) id ring).run after with
          | error e => rw [hp] at run; cases run
          | ok pair =>
            obtain ⟨found, finish⟩ := pair
            rw [hp] at run
            have pairs := Except.ok.inj run
            obtain ⟨resultEq, finalEq⟩ := Prod.mk.inj pairs
            have cutEq : found = cut := Option.some.inj (resultEq.trans same)
            subst found
            subst final
            exact (publicationSelected_authenticated (Campaign2.Product.snapshot after) id ring
              ⟨d, ring, hdev, hc⟩ after cut finish rfl hp).2.2

/-- The copied prefix and complete original run start from the same concrete
state. Exact source factoring supplies the actual intermediate publication. -/
theorem observedDecryptStep_authenticated (softirq irqExit : Leanux.M Unit) :
    Campaign2.Product.Ensures (observedDecryptStep softirq irqExit) (fun _ => True)
      (fun result _ => PublicationObservation result) := by
  intro initial result final _ run
  change ((decryptStep softirq irqExit).run initial >>= fun out =>
    Except.ok ((out.1, Campaign2.Product.observeResult ((publicationPrefix softirq).run initial)), out.2)) =
    Except.ok (result, final) at run
  cases whole : (decryptStep softirq irqExit).run initial with
  | error e => rw [whole] at run; cases run
  | ok pair =>
    obtain ⟨consumed, finish⟩ := pair
    rw [whole] at run
    obtain ⟨resultEq, finalEq⟩ := Prod.mk.inj (Except.ok.inj run)
    subst result
    have factored := whole
    rw [decryptStep_publication, StateT.run_bind] at factored
    cases hpref : (publicationPrefix softirq).run initial with
    | error e => rw [hpref] at factored; cases factored
    | ok pair =>
      obtain ⟨found, atCut⟩ := pair
      rw [hpref] at factored
      have suffix : (publicationSuffix softirq irqExit found).run atCut = .ok (consumed, finish) := factored
      refine ⟨found, Campaign2.Product.snapshot atCut, ?_,
        publicationSuffix_result softirq irqExit found atCut consumed finish trivial suffix, ?_⟩
      · rfl
      · exact publicationPrefix_authenticated softirq initial found atCut trivial hpref

end Leanux.Proofs.WG.Roaming
