import Leanux.Proofs.WG.Lifetimes.Enqueue

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Same-identity raw keypair updates and access-free kernel frames for mixed
observations. The setter contract requires equality with the current resident stamp. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem identity_sameKernel (ha : SameKernel a) : SameView identityView a := by
  intro w x v hr
  unfold identityView Peers.snapshot keypairResidents packetResidents
  rw [ha w x v hr]

theorem mixed_kernel (P : IdentityView → Prop) (a : M α) (ha : SameKernel a) :
    MixedSpec P (liftPrefix a) (fun _ => P) := mixed_lift P a (identity_sameKernel ha)

theorem mixed_pure (P : IdentityView → Prop) (x : α) :
    MixedSpec P (pure x) (fun _ => P) :=
  PrefixEnsures.pure (fun _ _ hi => hi.1.safe) (fun _ _ hi => hi)

theorem mixed_forget (hg : MixedSpec P g Q) (hq : ∀ x s, Q x s → R x s) : MixedSpec P g R :=
  hg.consequence (fun _ _ hi => hi) (fun x _ _ hi => ⟨hi.1, hq x _ hi.2⟩)

theorem mixed_branch (P : IdentityView → Prop) (d : Decision) (b : Bool) :
    MixedSpec P (liftPrefix (branch d b)) (fun _ => P) :=
  mixed_kernel P _ (sameKernel_branch d b)

theorem mixed_invariant (P : IdentityView → Prop) (why : String) :
    MixedSpec P (liftPrefix (invariant (α := α) why)) (fun _ => P) := by
  apply mixed_kernel
  intro w x v hr
  simp [invariant] at hr

theorem mixed_getKeypair_frame (P : IdentityView → Prop) (id : KeypairId) :
    MixedSpec P (getKeypairPrefix id) (fun _ => P) :=
  mixed_forget (mixed_getKeypair P id) (fun _ _ hi => hi.1)

theorem MixedInv.keyWrite {id stamp : Nat} (hi : MixedInv h w)
    (hl : keypairResidents w id = some stamp) :
    MixedInv (h ++ [.keypair (.write id stamp)]) w := by
  constructor
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.peer?] using hi.peer
  · simpa [List.filterMap_append, LifetimeEvent.keypair?] using hi.keypair.write hl
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.packet?] using hi.packet

theorem setKeypair_identity (id : KeypairId) (k : Keypair) (w v : World)
    (live : keypairResidents w id = some k.internalId)
    (hr : (setKeypair id k).run w = .ok ((), v)) : identityView v = identityView w := by
  cases hr
  apply Prod.ext
  · unfold identityView Peers.snapshot
    simp [Option.bind_map, Function.comp_def]
  · apply Prod.ext
    · funext j
      change keypairResidents _ j = keypairResidents w j
      cases hd : w.k.wg with
      | none => simp [keypairResidents, hd]
      | some d =>
        simp only [keypairResidents, hd, Option.bind_some] at live
        simp only [keypairResidents, hd, Option.map_some, Option.bind_some,
          Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq]
        by_cases hj : id = j
        · subst j
          simpa only [ite_true, Option.map_some] using live.symm
        · simp only [if_neg hj]
    · unfold identityView packetResidents
      simp [Option.bind_map, Function.comp_def]

theorem mixed_setKeypair (P : IdentityView → Prop) (id : KeypairId) (k : Keypair) :
    MixedSpec (fun s => P s ∧ s.2.1 id = some k.internalId)
      (setKeypairPrefix id k) (fun _ => P) := by
  intro w h hi
  rw [setKeypairPrefix_run]
  cases hd : w.k.wg with
  | none => simp [identityView, keypairResidents, hd] at hi
  | some d =>
    have hr : (setKeypair id k).run w = .ok ((),
        {w with k := {w.k with wg := some {d with keypairs := d.keypairs.insert id k}}}) := by
      simp [setKeypair, modifyDev, modifyK, hd]
    rw [hr]
    simp only [Option.isSome_some, ↓reduceIte]
    have he := setKeypair_identity id k w _ hi.2.2 hr
    have hn := (hi.1.keyWrite hi.2.2).congr he
    exact ⟨[.keypair (.write id k.internalId)], rfl, hn.safe, hn, he ▸ hi.2.1⟩

end Leanux.Proofs.WG.Lifetimes
