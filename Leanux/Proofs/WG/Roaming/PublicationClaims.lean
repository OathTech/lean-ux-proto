import Leanux.Proofs.WG.Roaming.PublicationSource
import Leanux.Proofs.WG.Roaming.Authentication
import Leanux.Proofs.WG.Roaming.PublicationFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Normal original decryption necessarily read a resident keypair, even if
its later validity, allocation or AEAD test returned none. -/
theorem decryptPacket_key_present (pkt : RxPacket) (w final : World)
    (result : Option RxPacket) (run : (decryptPacket pkt).run w = .ok (result, final)) :
    ∃ key, (w.k.wg.bind fun d => d.keypairs[pkt.keypair]?) = some key := by
  cases hd : w.k.wg with
  | none =>
    simp [decryptPacket, getKeypair, getDev, getK, branch, invariant,
      StateT.run_bind, StateT.run_pure, hd] at run
    change Except.error _ = Except.ok (result, final) at run
    cases run
  | some d =>
    cases hk : d.keypairs[pkt.keypair]? with
    | none =>
      simp [decryptPacket, getKeypair, getDev, getK, branch, invariant,
        StateT.run_bind, StateT.run_pure, hd, hk] at run
      change Except.error _ = Except.ok (result, final) at run
      cases run
    | some key => exact ⟨key, by simp [hd, hk]⟩

theorem decryptPacket_authentication_at (pkt : RxPacket) (before : Campaign2.Snapshot) :
    Ensures (decryptPacket pkt) (fun w => Campaign2.snapshot w = before)
      (fun result _ => ∀ plain, result = some plain → ∃ key,
        keyAt before pkt.keypair = some key ∧
        plain.source = pkt.source ∧ plain.peer = pkt.peer ∧ plain.keypair = pkt.keypair ∧
        plain.nonce = u64le pkt.bytes 8 ∧
        aeadDecrypt key.receiving.key (counterNonce (u64le pkt.bytes 8))
          (pkt.bytes.drop 16) [] = some plain.bytes) := by
  intro w result final pre run plain same
  obtain ⟨key, resident⟩ := decryptPacket_key_present pkt w final result run
  refine ⟨key, ?_, decryptPacket_authenticated pkt key w result final resident run plain same⟩
  subst before
  exact resident

/-- Publishing the selected state preserves the packet's other fields. The
held owner reference and callback-entry snapshot come from the original prefix. -/
theorem enqueuePublication_packet (id : SkbId) (state : PacketState) (P : RxPacket → Prop) :
    Ensures (enqueuePublication id state)
      (fun w => ∀ p, packetAt (Campaign2.snapshot w) id = some p → P p)
      (fun result w => result.2 = Campaign2.snapshot w ∧ ∃ p,
        P p ∧ packetAt result.2 id = some { p with state }) := by
  rw [ensures_iff]
  have hr := refcountInc_kernel_frame
    (fun k => ∀ p, (k.wg.bind fun d => d.rxSkbs[id]?) = some p → P p)
  have hread := read_snapshot (fun w => ∃ p, P p ∧
    packetAt (Campaign2.snapshot w) id = some { p with state })
  mvcgen [enqueuePublication, IndexOwner.peerDeref, IndexOwner.peerWord,
    peerGet, requireNotPending, hr, getRxSkb, setRxSkb,
    getKeypair, getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    branch, branchCmp, invariant, unsupported, hread]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [packetAt, Campaign2.snapshot, Campaign2.core,
    Std.TreeMap.getElem?_insert]
  all_goals grind

theorem setRxSkb_plain (id : SkbId) (plain : RxPacket) :
    ⦃fun _ => ⌜True⌝⦄ setRxSkb id (fun _ => plain)
      ⦃⇓? _ w => ⌜packetAt (Campaign2.snapshot w) id = some plain⌝⦄ := by
  mvcgen [setRxSkb, getRxSkb, getDev, getK, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [packetAt, Campaign2.snapshot, Campaign2.core]

theorem publicationPublish_packet (id : SkbId) (decrypted : Option RxPacket) :
    Ensures (publicationPublish id decrypted) (fun _ => True)
      (fun result w => result.2 = Campaign2.snapshot w ∧ ∃ published,
        packetAt result.2 id = some published ∧
        published.state = (if decrypted.isSome then .crypted else .dead) ∧
        ∀ plain, decrypted = some plain → published = { plain with state := .crypted }) := by
  rw [ensures_iff]
  cases decrypted with
  | none =>
    have hp := (ensures_iff _ _ _).mp (enqueuePublication_packet id .dead (fun _ => True))
    mvcgen [publicationPublish, branch, invariant, hp]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all
    all_goals grind
  | some plain =>
    have hs := setRxSkb_plain id plain
    have hp := (ensures_iff _ _ _).mp (enqueuePublication_packet id .crypted (fun p => p = plain))
    mvcgen [publicationPublish, branch, invariant, hs, hp]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all
    all_goals grind

/-- The original packet getter reads without changing the execution state. -/
theorem getRxSkb_read (id : SkbId) (entry : World) :
    Ensures (getRxSkb id) (fun w => w = entry)
      (fun p w => w = entry ∧ packetAt (Campaign2.snapshot entry) id = some p) := by
  rw [ensures_iff]
  mvcgen [getRxSkb, getDev, getK, invariant]
  all_goals simp_all [packetAt, Campaign2.snapshot, Campaign2.core]

/-- The prefix's successful packet branch has the AEAD provenance at its
publication snapshot. The supplied ring fact is about the actual prior read. -/
theorem publicationPacket_authenticated (after : Campaign2.Snapshot) (id : SkbId)
    (selected : ∃ d ring, after.wg.device = some d ∧
      d.decryptQueue.consume = (some id, ring)) :
    Ensures (publicationPacket after id)
      (fun w => packetAt (Campaign2.snapshot w) id = packetAt after id)
      (fun cut w => cut.id = id ∧ cut.afterSoftirq = after ∧
        cut.publication = Campaign2.snapshot w ∧ PublishedAuthentication cut) := by
  intro w cut final same run
  simp only [publicationPacket, StateT.run_bind] at run
  cases hg : (getRxSkb id).run w with
  | error e => rw [hg] at run; cases run
  | ok pair =>
    obtain ⟨pkt, before⟩ := pair
    obtain ⟨unchanged, resident⟩ := getRxSkb_read id w w pkt before rfl hg
    subst before
    rw [hg] at run
    change ((decryptPacket pkt).run w >>= fun dec =>
      (publicationPublish id dec.1).run dec.2 >>= fun pub =>
        Except.ok (PublicationCut.mk after (Campaign2.snapshot w) id pub.1.1 pkt dec.1 pub.1.2, pub.2)) =
      Except.ok (cut, final) at run
    cases hd : (decryptPacket pkt).run w with
    | error e => rw [hd] at run; cases run
    | ok pair =>
      obtain ⟨decrypted, next⟩ := pair
      rw [hd] at run
      change ((publicationPublish id decrypted).run next >>= fun pub =>
        Except.ok (PublicationCut.mk after (Campaign2.snapshot w) id pub.1.1 pkt decrypted pub.1.2, pub.2)) =
        Except.ok (cut, final) at run
      cases hp : (publicationPublish id decrypted).run next with
      | error e => rw [hp] at run; cases run
      | ok pair =>
        obtain ⟨published, finish⟩ := pair
        rw [hp] at run
        change Except.ok (PublicationCut.mk after (Campaign2.snapshot w) id published.1 pkt decrypted published.2,
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
            have auth := decryptPacket_authentication_at pkt (Campaign2.snapshot w)
              w decrypted next rfl hd plain he
            obtain ⟨key, keyread, source, peer, keypair, nonce, aead⟩ := auth
            have output := plaintext plain he
            exact ⟨key, keyread, by simpa [output] using source,
              by simpa [output] using peer, by simpa [output] using keypair,
              by simpa [output] using nonce, by simpa [output] using aead⟩

theorem publicationSelected_authenticated (after : Campaign2.Snapshot) (id : SkbId)
    (ring : PtrRing SkbId)
    (selected : ∃ d rest, after.wg.device = some d ∧
      d.decryptQueue.consume = (some id, rest)) :
    Ensures (publicationSelected after id ring)
      (fun w => packetAt (Campaign2.snapshot w) id = packetAt after id)
      (fun cut w => cut.id = id ∧ cut.afterSoftirq = after ∧
        cut.publication = Campaign2.snapshot w ∧ PublishedAuthentication cut) := by
  have hp := (ensures_iff _ _ _).mp (publicationPacket_authenticated after id selected)
  rw [ensures_iff]
  mvcgen [publicationSelected, branch, modifyDev, modifyK, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [packetAt, Campaign2.snapshot, Campaign2.core,
    Option.bind_map, Function.comp_def]

theorem publicationPrefix_authenticated (softirq : M Unit) :
    Ensures (publicationPrefix softirq) (fun _ => True)
      (fun result w => ∀ cut, result = some cut →
        cut.publication = Campaign2.snapshot w ∧ PublishedAuthentication cut) := by
  intro initial result final _ run cut same
  simp only [publicationPrefix, StateT.run_bind] at run
  cases hs : softirq.run initial with
  | error e => rw [hs] at run; cases run
  | ok pair =>
    obtain ⟨unit, after⟩ := pair
    rw [hs] at run
    change ((getDev).run after >>= fun out =>
      (match out.1.decryptQueue.consume with
       | (none, _) => do
         _ ← branch .decWorkerConsumed false
         pure none
       | (some id, ring) => do
         let c ← publicationSelected (Campaign2.snapshot after) id ring
         pure (some c)).run out.2) = Except.ok (result, final) at run
    cases hdev : after.k.wg with
    | none =>
      have absent : getDev.run after = .error (.invariant "no WireGuard device in this trace's fixture") := by
        simp [getDev, getK, StateT.run_bind, invariant, hdev]
        rfl
      rw [absent] at run
      cases run
    | some d =>
      have resident : getDev.run after = .ok (d, after) := by
        simp [getDev, getK, StateT.run_bind, hdev]
        rfl
      rw [resident] at run
      change (match d.decryptQueue.consume with
        | (none, _) => do
          _ ← branch .decWorkerConsumed false
          pure none
        | (some id, ring) => do
          let c ← publicationSelected (Campaign2.snapshot after) id ring
          pure (some c)).run after = Except.ok (result, final) at run
      cases hc : d.decryptQueue.consume with
      | mk first ring =>
        cases first with
        | none =>
          simp only [hc] at run
          change ((branch .decWorkerConsumed false).run after >>= fun out =>
            Except.ok (none, out.2)) = Except.ok (result, final) at run
          cases hb : (branch .decWorkerConsumed false).run after with
          | error e => rw [hb] at run; cases run
          | ok pair =>
            rw [hb] at run
            have impossible : none = result := congrArg Prod.fst (Except.ok.inj run)
            rw [← impossible] at same
            cases same
        | some id =>
          simp only [hc] at run
          change ((publicationSelected (Campaign2.snapshot after) id ring).run after >>= fun out =>
            Except.ok (some out.1, out.2)) = Except.ok (result, final) at run
          cases hp : (publicationSelected (Campaign2.snapshot after) id ring).run after with
          | error e => rw [hp] at run; cases run
          | ok pair =>
            obtain ⟨found, finish⟩ := pair
            rw [hp] at run
            have pairs := Except.ok.inj run
            obtain ⟨resultEq, finalEq⟩ := Prod.mk.inj pairs
            have cutEq : found = cut := Option.some.inj (resultEq.trans same)
            subst found
            subst final
            exact (publicationSelected_authenticated (Campaign2.snapshot after) id ring
              ⟨d, ring, hdev, hc⟩ after cut finish rfl hp).2.2

theorem publicationSuffix_result (softirq irqExit : M Unit) (cut : Option PublicationCut) :
    Ensures (publicationSuffix softirq irqExit cut) (fun _ => True)
      (fun result _ => result = cut.isSome) := by
  have hs := unconstrained_prefix softirq
  have hi := unconstrained_prefix irqExit
  have hp := fun pid => unconstrained_prefix (peerPut (some pid))
  rw [ensures_iff]
  mvcgen [publicationSuffix, hs, hi, hp]

/-- The copied prefix and complete original run start from the same concrete
state. Exact source factoring supplies the actual intermediate publication. -/
theorem observedDecryptStep_authenticated (softirq irqExit : M Unit) :
    Campaign2.Ensures (observedDecryptStep softirq irqExit) (fun _ => True)
      (fun result _ => PublicationObservation result) := by
  intro initial result final _ run
  change ((decryptStep softirq irqExit).run initial >>= fun out =>
    Except.ok ((out.1, Campaign2.observeResult ((publicationPrefix softirq).run initial)), out.2)) =
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
      refine ⟨found, Campaign2.snapshot atCut, ?_,
        publicationSuffix_result softirq irqExit found atCut consumed finish trivial suffix, ?_⟩
      · simp only [hpref]
        rfl
      · exact publicationPrefix_authenticated softirq initial found atCut trivial hpref

end Leanux.Proofs.WG.Roaming
