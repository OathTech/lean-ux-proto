import Leanux.Proofs.WG.Lifetimes.MixedFrames

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Same-identity raw keypair updates and access-free store frames for mixed
observations. The setter contract requires equality with the current resident stamp. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

/-- The identity observation factors through the original seven WG store fields.
The action still runs in its actual state and monad. -/
theorem identity_sameWGStore
    {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => wgStoreView (project s)) a) :
    SameView (fun s => identityView (project s)) a := by
  let observe : WGStoreView → IdentityView := fun s =>
    (⟨s.peerCounter, fun i => (s.dev.bind fun d => d.peers[i]?).map (·.internalId)⟩,
      (fun i => (s.dev.bind fun d => d.keypairs[i]?).map (·.internalId)),
      fun slot => s.dev.bind fun d => match slot with
        | .inl i => d.txSkbs[i]?.map (fun _ => (d.ifindex, i + 1))
        | .inr i => d.rxSkbs[i]?.map (fun _ => (d.ifindex, i + 1)))
  exact ha.of_factor observe (fun s => identityView (project s)) (fun _ => rfl)

/-- Generic prefix contracts retain arbitrary actual states, including World. -/
abbrev ProjectedMixedSpec {S : Type} (project : S → WGWorld)
    (P : IdentityView → Prop) (g : PrefixT LifetimeEvent S α)
    (Q : α → IdentityView → Prop) :=
  PrefixEnsures (fun h w => MixedInv h (project w) ∧ P (identityView (project w)))
    LifetimeEvent.Safe g
    (fun x h w => MixedInv h (project w) ∧ Q x (identityView (project w)))

theorem mixed_store {S : Type} (project : S → WGWorld) (P : IdentityView → Prop)
    (a : StateT S (Except Stop) α) (ha : SameView (fun s => wgStoreView (project s)) a) :
    ProjectedMixedSpec project P (liftPrefix a) (fun _ => P) :=
  mixed_lift project P a (identity_sameWGStore ha)

theorem mixed_pure {S : Type} (project : S → WGWorld) (P : IdentityView → Prop) (x : α) :
    ProjectedMixedSpec project P (pure x) (fun _ => P) :=
  PrefixEnsures.pure (fun _ _ hi => hi.1.safe) (fun _ _ hi => hi)

theorem mixed_forget {S : Type} {project : S → WGWorld}
    {P : IdentityView → Prop} {g : PrefixT LifetimeEvent S α}
    {Q R : α → IdentityView → Prop}
    (hg : ProjectedMixedSpec project P g Q) (hq : ∀ x s, Q x s → R x s) :
    ProjectedMixedSpec project P g R :=
  hg.consequence (fun _ _ hi => hi) (fun x _ _ hi => ⟨hi.1, hq x _ hi.2⟩)

theorem mixed_state_forget (hg : MixedSpec P g Q) (hq : ∀ x s, Q x s → R x s) :
    MixedSpec P g R :=
  hg.consequence (fun _ _ _ hi => hi) (fun x _ _ _ hi => ⟨hi.1, hq x _ hi.2⟩)

theorem mixed_branch (P : IdentityView → Prop) (d : Decision) (b : Bool) :
    MixedSpec P (liftWGPrefix (branch d b)) (fun _ => P) := by
  apply mixed_state_lift
  intro initial
  exact hoare_liftAmbient (AmbientM.branch d b) (fun w : WGWorld => identityView w = initial)

theorem mixed_invariant (P : IdentityView → Prop) (why : String) :
    MixedSpec P (liftWGPrefix (invariant (α := α) why)) (fun _ => P) := by
  apply mixed_state_lift
  intro initial
  exact hoare_liftAmbient (AmbientM.invariant (α := α) why)
    (fun w : WGWorld => identityView w = initial)

theorem mixed_getKeypair_frame (P : IdentityView → Prop) (id : KeypairId) :
    MixedSpec P (getKeypairPrefix id) (fun _ => P) :=
  mixed_state_forget (mixed_getKeypair P id) (fun _ _ hi => hi.1)

theorem MixedInv.keyWrite {id stamp : Nat} (hi : MixedInv h w)
    (hl : keypairResidents w id = some stamp) :
    MixedInv (h ++ [.keypair (.write id stamp)]) w := by
  constructor
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.peer?] using hi.peer
  · simpa [List.filterMap_append, LifetimeEvent.keypair?] using hi.keypair.write hl
  · simpa [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, LifetimeEvent.packet?] using hi.packet

theorem setKeypair_identity (id : KeypairId) (k : Keypair) (w v : WGWorld) (ambient ambient' : Ambient)
    (live : keypairResidents w id = some k.internalId)
    (hr : ((setKeypair id k).run w).run ambient = .ok (((), v), ambient')) : identityView v = identityView w := by
  cases hr
  apply Prod.ext
  · unfold identityView Peers.snapshot
    simp [Option.bind_map, Function.comp_def]
  · apply Prod.ext
    · funext j
      change keypairResidents _ j = keypairResidents w j
      cases hd : w.dev with
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
  intro w ambient h hi
  rw [show runPrefix ((setKeypairPrefix id k).run w) ambient h =
      runStatePrefix (setKeypairPrefix id k) w ambient h from rfl, setKeypairPrefix_run]
  cases hd : w.dev with
  | none => simp [identityView, keypairResidents, hd] at hi
  | some d =>
    have hr : ((setKeypair id k).run w).run ambient = .ok (((),
        {w with dev := some {d with keypairs := d.keypairs.insert id k}}), ambient) := by
      simp [setKeypair, modifyDev, hd]
    rw [hr]
    simp only [Option.isSome_some, ↓reduceIte]
    have he := setKeypair_identity id k w _ ambient ambient hi.2.2 hr
    have hn := (hi.1.keyWrite hi.2.2).congr he
    exact ⟨[.keypair (.write id k.internalId)], rfl, hn.safe, hn, he ▸ hi.2.1⟩

end Leanux.Proofs.WG.Lifetimes
