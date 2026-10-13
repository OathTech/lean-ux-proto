import Leanux.Proofs.WG.Keypairs.Ordinary

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Keypairs
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing Leanux.Proofs.Framing.Allocation

/-- The same decreasing encounter count applies at every allocation site. -/
theorem hiddenAlloc_sameKernel (site : AllocSite) : SameKernel (hiddenAlloc site) := by
  apply sameKernel_of_wp
  intro k
  rw [← allocationOutcome_eq]
  mvcgen [allocationOutcome, recordOutcome, placeholderOutcome, hidden, skipAmbient, invariant, unsupported]
  invariants
  | inv1 _ n _ _ _ _ _ _ => fun r _ => ⟨n - r.2 + 1⟩
  | inv2 => ((⇓? _ w => ⌜w.k = k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (letI : Nonempty World := ⟨by assumption⟩; infer_instance)
  all_goals try simp_all [WhileVariant.eval, SVal.evalsTo, SVal.uncurry]
  all_goals omega

theorem hiddenClock_sameKernel (site : HiddenSite) : SameKernel (hiddenClock site) := by
  apply sameKernel_of_wp
  intro k
  have hs := sameKernel_wp _ (hidden_sameKernel site) (fun k' => k' = k)
  mvcgen [hiddenClock, hs]

theorem birthdateHasExpired_sameKernel (birthday : Int) (seconds : Nat) :
    SameKernel (birthdateHasExpired birthday seconds) := by
  apply sameKernel_of_wp
  intro k
  have hs := sameKernel_wp _ (hiddenClock_sameKernel .birthdateExpired) (fun k' => k' = k)
  mvcgen [birthdateHasExpired, hs]

theorem kdf_sameKernel (second third : Bool) (chainingKey data : List UInt8) :
    SameKernel (kdf second third chainingKey data) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [kdf, Leanux.WG.orM, branch]

theorem kdfOut_sameKernel (outs : List (List UInt8)) (i : Nat) :
    SameKernel (kdfOut outs i) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [kdfOut, invariant]

theorem deriveKeys_sameSnapshot (kp : KeypairId) (initiator : Bool) (chainingKey : List UInt8) :
    SameSnapshot (deriveKeys kp initiator chainingKey) := by
  apply sameSnapshot_of_wp
  intro s
  have clock_spec := (sameSnapshot_of_sameKernel (hiddenClock_sameKernel .deriveKeysBirthdate)).wp (fun t => t = s)
  have kdf_spec := (sameSnapshot_of_sameKernel (kdf_sameKernel true false chainingKey [])).wp (fun t => t = s)
  have out_spec := fun outs i => (sameSnapshot_of_sameKernel (kdfOut_sameKernel outs i)).wp (fun t => t = s)
  mvcgen [deriveKeys, clock_spec, kdf_spec, out_spec,
    getKeypair, getDev, getK, setKeypair, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [snapshot]
  all_goals try subst s
  all_goals
    split
    all_goals
      calc
        _ = _ := by apply mapSnapshot_insert_same <;> first | assumption | rfl
        _ = _ := by assumption

theorem getKeypair_snapshot_wp (i : Nat) (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ getKeypair i
    ⦃⇓? k w => ⌜P (snapshot w) ∧ (snapshot w).slots i = some (cell k)⌝⦄ := by
  mvcgen [getKeypair, getDev, getK, invariant]
  all_goals simp_all [snapshot]

theorem setKeypair_snapshot_wp (i : Nat) (k : Keypair) (P : Snapshot → Prop) :
    ⦃fun w => ⌜P (snapshot w) ∧ (snapshot w).slots i = some (cell k)⌝⦄ setKeypair i k
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x w' hp hr
  cases hd : w.k.wg with
  | none => simp [snapshot, hd] at hp
  | some d =>
    have hs : (setKeypair i k).run w = .ok ((), Leanux.Proofs.WG.CounterWindow.store w i k) := rfl
    rw [hs] at hr
    cases hr
    rw [snapshot_store w d i k hd, put_existing _ _ _ hp.2]
    exact hp.1

theorem decryptPacket_sameSnapshot (pkt : RxPacket) : SameSnapshot (decryptPacket pkt) := by
  apply sameSnapshot_of_wp
  intro s
  have birthday_spec := fun birth seconds =>
    (sameSnapshot_of_sameKernel (birthdateHasExpired_sameKernel birth seconds)).wp (fun t => t = s)
  have alloc_spec := (sameSnapshot_of_sameKernel (hiddenAlloc_sameKernel .skbCowDataRx)).wp (fun t => t = s)
  have get_spec := fun i => getKeypair_snapshot_wp i (fun t => t = s)
  have set_spec := fun i k => setKeypair_snapshot_wp i k (fun t => t = s)
  mvcgen [decryptPacket, birthday_spec, alloc_spec, Leanux.WG.orM, branch,
    get_spec, set_spec, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [snapshot, cell]

end Leanux.Proofs.WG.Keypairs
