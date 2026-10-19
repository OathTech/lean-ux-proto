import Leanux.Proofs.Framing.Basic
import Leanux.Proofs.Framing.Allocation
import Leanux.Proofs.Framing.Index
import Leanux.Proofs.Framing.Lift

set_option pp.structureInstances false

namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing.Allocation

theorem branch_wp (d : Decision) (b : Bool) :
    ⦃fun (_ : Ambient) => ⌜True⌝⦄ AmbientM.branch d b ⦃⇓? x _ => ⌜x = b⌝⦄ := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x w' _ hr
  change Except.ok (b, _) = Except.ok (x, w') at hr
  cases hr
  rfl

theorem getKeypair_wp (query slot stamp : Nat) (counter : ReplayCounter) :
    ⦃fun w => ⌜Protected slot stamp counter w⌝⦄ getKeypair query
    ⦃⇓? k w => ⌜Protected slot stamp counter w ∧
      (query = slot → k.internalId = stamp → k.receivingCounter = counter)⌝⦄ :=
  (hoare_iff_triple _ _ _).mp (getKeypair_spec query slot stamp counter)

theorem setKeypair_wp (query slot stamp : Nat) (counter : ReplayCounter) (k : Keypair) :
    ⦃fun w => ⌜Protected slot stamp counter w ∧
      (query = slot → k.internalId = stamp → k.receivingCounter = counter)⌝⦄
    setKeypair query k ⦃⇓? _ w => ⌜Protected slot stamp counter w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient a w' ambient' hp hr
  exact (hoare_iff_run_ambient _ _ _).mp
    (setKeypair_preserves query slot stamp counter k hp.2) w ambient a w' ambient' hp.1 hr

theorem keypairGet_preserves (kp : Option KeypairId) (slot stamp : Nat)
    (counter : ReplayCounter) :
    Preserves (Protected slot stamp counter) (keypairGet kp) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hp hr
  cases kp with
  | none =>
    simp [keypairGet, branch, AmbientM.branch] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    exact hp
  | some id =>
    cases hd : w.dev with
    | none =>
      simp [keypairGet, getKeypair, getDev, hd, branch, AmbientM.branch,
        invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hk : d.keypairs[id]? with
      | none =>
        simp [keypairGet, getKeypair, getDev, hd, hk, branch, AmbientM.branch,
          invariant, AmbientM.invariant] at hr
        cases hr
      | some key =>
        simp only [keypairGet, getKeypair, getDev, setKeypair, modifyDev,
          branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, refcountIncNotZero,
          unsupported, invariant, AmbientM.unsupported, AmbientM.invariant,
          StateT.run_bind] at hr
        simp [hd, hk] at hr
        split at hr <;> simp_all
        all_goals try split at hr <;> simp_all
        all_goals try split at hr <;> simp_all
        all_goals try split at hr <;> simp_all
        all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        all_goals
          first
          | exact hp
          | refine ⟨hp.1, ?_⟩
            intro d' k hd' hk' hi
            cases hd'
            simp only [Std.TreeMap.getElem?_insert] at hk'
            by_cases he : id = slot
            · subst id
              simp at hk'
              subst k
              exact hp.2 d key hd hk hi
            · simp [he] at hk'
              exact hp.2 d k hd hk' hi

/-- Resolving an embedded peer word reads its owner without changing the
WireGuard state. This is not an access-coverage claim. -/
theorem indexOwner_peerWord_preserves (owner : IndexOwner) (P : WGWorld → Prop) :
    Preserves P owner.peerWord := by
  have device : Preserves P getDev := by
    unfold getDev
    apply preserves_bind (hoare_consequence (hoare_get P)
      (fun _ h => h) (fun _ _ h => h.2))
    intro w
    cases w.dev
    · exact hoare_liftAmbient (AmbientM.invariant _) P
    · exact preserves_pure _
  have peer (id : PeerId) : Preserves P (getPeer id) := by
    unfold getPeer
    apply preserves_bind device
    intro d
    cases h : d.peers.get? id
    · exact hoare_liftAmbient (AmbientM.invariant _) P
    · exact preserves_pure _
  have key (id : KeypairId) : Preserves P (getKeypair id) := by
    unfold getKeypair
    apply preserves_bind device
    intro d
    cases h : d.keypairs.get? id
    · exact hoare_liftAmbient (AmbientM.invariant _) P
    · exact preserves_pure _
  cases owner with
  | handshake id =>
    exact preserves_bind (peer id) (fun p => preserves_pure p.handshakeEntryPeer)
  | keypair id =>
    exact preserves_bind (key id) (fun k => preserves_pure k.peer)

theorem indexOwner_peerDeref_preserves (owner : IndexOwner) (P : WGWorld → Prop) :
    Preserves P owner.peerDeref := by
  unfold IndexOwner.peerDeref
  apply preserves_bind (indexOwner_peerWord_preserves owner P)
  intro word
  cases word with
  | none => exact hoare_liftAmbient (AmbientM.unsupported _) P
  | some pid => exact preserves_pure pid

theorem keypairPut_preserves (kp : Option KeypairId) (now : Bool) (slot stamp : Nat)
    (counter : ReplayCounter) :
    Preserves (Protected slot stamp counter) (keypairPut kp now) := by
  let P := Protected slot stamp counter
  have erase (id : KeypairId) :
      Preserves P (modifyDev fun d => {d with keypairs := d.keypairs.erase id}) := by
    apply hoare_modify
    intro w hp
    refine ⟨hp.1, ?_⟩
    intro d key hd hk hi
    cases hw : w.dev with
    | none => simp [hw] at hd
    | some old =>
      simp only [hw, Option.map_some, Option.some.injEq] at hd
      subst d
      simp only [Std.TreeMap.getElem?_erase] at hk
      split at hk
      · cases hk
      · exact hp.2 old key hw hk hi
  have rc (old : Nat) : Preserves P (refcountDecAndTest old : WG.M Bool) := by
    let finish : WG.M Bool := do
      if ← branch .refcountSubNonpositive (old == 0) then
        unsupported "refcount_warn_saturate (use after free)"
      if ← branch .refcountSubUnderflow (old < 1) then
        unsupported "refcount_warn_saturate (underflow)"
      return false
    have finishP : Preserves P finish := by
      unfold finish
      apply preserves_bind (hoare_liftAmbient
        (AmbientM.branch .refcountSubNonpositive (old == 0)) P)
      intro bad
      cases bad with
      | true =>
        apply (hoare_iff_run_ambient _ _ _).mpr
        intro w a x w' a' _ hr
        change Except.error _ = Except.ok _ at hr
        cases hr
      | false =>
        apply preserves_bind (hoare_liftAmbient
          (AmbientM.branch .refcountSubUnderflow (old < 1)) P)
        intro bad
        cases bad with
        | true =>
          apply (hoare_iff_run_ambient _ _ _).mpr
          intro w a x w' a' _ hr
          change Except.error _ = Except.ok _ at hr
          cases hr
        | false => exact preserves_pure false
    unfold refcountDecAndTest
    apply preserves_bind (hoare_liftAmbient
      (AmbientM.branchCmp .refcountSubPositive (old > 0) old 0) P)
    intro positive
    cases positive with
    | false => exact finishP
    | true =>
      apply preserves_bind (hoare_liftAmbient
        (AmbientM.branchCmp .refcountSubToZero (old == 1) old 1) P)
      intro released
      cases released
      · exact finishP
      · exact preserves_pure true
  unfold keypairPut
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .keypairPutNull kp.isNone) P)
  intro null
  cases null with
  | true => exact preserves_pure ()
  | false =>
    cases kp with
    | none => exact hoare_liftAmbient (AmbientM.invariant "unreachable") P
    | some id =>
      apply hoare_bind _ _ (getKeypair_spec id slot stamp counter)
      intro key
      dsimp only
      let q := id = slot → key.internalId = stamp → key.receivingCounter = counter
      let tail : WG.M Unit := do
        setKeypair id {key with refcount := key.refcount - 1}
        if ← branch .keypairKrefPutReleased (← refcountDecAndTest key.refcount) then
          _ ← IndexOwner.peerDeref (.keypair id)
          (indexRemove (.keypair id) : WG.M Unit)
          modifyDev fun d => {d with keypairs := d.keypairs.erase id}
      have tailP : Hoare tail (fun w => P w ∧ q) (fun _ => P) := by
        unfold tail
        apply hoare_bind _ _ (setKeypair_wp id slot stamp counter
          {key with refcount := key.refcount - 1})
        intro _
        apply preserves_bind (rc key.refcount)
        intro released
        apply preserves_bind (hoare_liftAmbient
          (AmbientM.branch .keypairKrefPutReleased released) P)
        intro free
        cases free with
        | false => exact preserves_pure ()
        | true =>
          apply preserves_bind (indexOwner_peerDeref_preserves _ P)
          intro _
          apply preserves_bind
          · rw [indexRemove_eq]
            apply hoare_liftIndex
            intro g d table hp hd
            refine ⟨hp.1, ?_⟩
            intro d' k hd' hk hi
            cases hd'
            exact hp.2 d k hd hk hi
          · intro _
            exact erase id
      apply hoare_bind _ _ (hoare_liftAmbient
        (AmbientM.branch .keypairPutUnreferenceNow now) (fun w => P w ∧ q))
      intro run
      cases run with
      | false =>
        simpa only [tail, Bool.false_eq_true, ite_false, bind_assoc] using tailP
      | true =>
        simp only [bind_assoc]
        apply hoare_bind _ _ (indexOwner_peerDeref_preserves _ (fun w => P w ∧ q))
        intro _
        apply hoare_bind
        · rw [indexRemove_eq]
          apply hoare_liftIndex
          intro g d table hp hd
          refine ⟨⟨hp.1.1, ?_⟩, hp.2⟩
          intro d' k hd' hk hi
          cases hd'
          exact hp.1.2 d k hd hk hi
        · intro _
          simpa only [tail, bind_assoc] using tailP

theorem keypairCreate_preserves (pid : Option PeerId) (slot stamp : Nat)
    (counter : ReplayCounter) :
    Preserves (Protected slot stamp counter) (keypairCreate pid) := by
  unfold keypairCreate
  apply preserves_bind (hoare_liftAmbient (AmbientM.hiddenAlloc .kzallocKeypair)
    (Protected slot stamp counter))
  intro allocated
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .keypairCreateNoMem (!allocated))
    (Protected slot stamp counter))
  intro failed
  cases failed with
  | true => exact preserves_pure none
  | false =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x w' ambient' hp hr
    cases hd : w.dev with
    | none =>
      simp [getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      simp [getDev, modifyDev, setKeypair, hd] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      refine ⟨Nat.le_trans hp.1 (Nat.le_succ _), ?_⟩
      intro d' key hd' hk hi
      cases hd'
      simp only [Std.TreeMap.getElem?_insert] at hk
      by_cases he : d.nextKeypairId = slot
      · simp [he] at hk
        subst key
        dsimp at hi
        have := hp.1
        omega
      · simp [he] at hk
        exact hp.2 d key hd hk hi

end Leanux.Proofs.Framing
