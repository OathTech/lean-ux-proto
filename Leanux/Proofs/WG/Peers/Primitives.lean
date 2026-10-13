import Leanux.Proofs.WG.Lifetimes.Actions
import Leanux.Proofs.WG.Keypairs.Frames.WGBase
import Leanux.WG.Peer

set_option pp.structureInstances false
set_option maxHeartbeats 800000

/-! Peer allocation identities for the current store. A raw slot reference is
not an ownership proof: in particular the dump-cursor counterexample can select
a newly allocated peer. These helpers prove only the identities they retain. -/
namespace Leanux.Proofs.WG.Peers
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Lifetimes

def mapStore (frontier : Nat) (peers : Std.TreeMap Nat Peer) : Store PeerId :=
  ⟨frontier, fun i => peers[i]?.map (·.internalId)⟩

def snapshot (w : World) : Store PeerId :=
  ⟨w.k.peerCounter, fun i => (w.k.wg.bind fun d => d.peers[i]?).map (·.internalId)⟩

theorem getPeer_current (i : PeerId) (w w' : World) (p : Peer)
    (hr : (getPeer i).run w = .ok (p, w')) :
    w' = w ∧ (snapshot w).slots i = some p.internalId := by
  cases hd : w.k.wg with
  | none => simp [getPeer, getDev, getK, hd, invariant] at hr
  | some d =>
    cases hp : d.peers[i]? with
    | none => simp [getPeer, getDev, getK, hd, hp, invariant] at hr
    | some old =>
      have he : (getPeer i).run w = .ok (old, w) := by
        simp [getPeer, getDev, getK, hd, hp]
      rw [he] at hr
      cases hr
      exact ⟨rfl, by simp [snapshot, hd, hp]⟩

theorem getPeer_spec (i : PeerId) (start : World) :
    ⦃fun w => ⌜w = start⌝⦄ getPeer i
    ⦃⇓? p w => ⌜w = start ∧ ∃ d, w.k.wg = some d ∧ d.peers[i]? = some p⌝⦄ := by
  apply (Leanux.Proofs.Framing.hoare_iff_triple _ _ _).mp
  intro w p w' hq hr
  cases hd : w.k.wg with
  | none => simp [getPeer, getDev, getK, hd, invariant] at hr
  | some d =>
    cases hp : d.peers[i]? with
    | none => simp [getPeer, getDev, getK, hd, hp, invariant] at hr
    | some old =>
      have he : (getPeer i).run w = .ok (old, w) := by
        simp [getPeer, getDev, getK, hd, hp]
      rw [he] at hr
      cases hr
      exact ⟨hq, d, hd, hp⟩

theorem mapStore_insert_same (frontier : Nat) (peers : Std.TreeMap Nat Peer)
    (i : PeerId) (old p : Peer) (hp : peers[i]? = some old)
    (hid : p.internalId = old.internalId) :
    mapStore frontier (peers.insert i p) = mapStore frontier peers := by
  apply Store.ext
  · rfl
  · funext j
    simp only [mapStore, Std.TreeMap.getElem?_insert]
    split <;> simp_all

theorem mapStore_insert_erase (frontier : Nat) (peers : Std.TreeMap Nat Peer)
    (i : PeerId) (p : Peer) :
    Retained (mapStore frontier peers) (mapStore frontier ((peers.insert i p).erase i)) := by
  have he : mapStore frontier ((peers.insert i p).erase i) =
      (mapStore frontier peers).put i none := by
    apply Store.ext
    · rfl
    · funext j
      simp only [mapStore, Store.put, Std.TreeMap.getElem?_erase,
        Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq]
      by_cases h : i = j <;> simp_all [eq_comm]
  rw [he]
  exact erase_retained _ _

theorem mapStore_insert_retained (frontier : Nat) (peers : Std.TreeMap Nat Peer)
    (i : PeerId) (old p : Peer) (hp : peers[i]? = some old)
    (hid : p.internalId = old.internalId) :
    Retained (mapStore frontier peers) (mapStore frontier (peers.insert i p)) := by
  rw [mapStore_insert_same frontier peers i old p hp hid]
  exact .refl _

theorem mapStore_insert_retained_stamp (frontier : Nat) (peers : Std.TreeMap Nat Peer)
    (i : PeerId) (p : Peer) (hp : (mapStore frontier peers).slots i = some p.internalId) :
    Retained (mapStore frontier peers) (mapStore frontier (peers.insert i p)) := by
  cases he : peers[i]? with
  | none => simp [mapStore, he] at hp
  | some old =>
    apply mapStore_insert_retained frontier peers i old p he
    simpa [mapStore, he] using hp.symm

/-- The raw setter preserves identities only when replacing a currently
resident peer by a peer with that same identity. The premise excludes arbitrary
old-identity insertion through this otherwise unconditional mirror setter. -/
theorem setPeer_same (i : PeerId) (p : Peer) (w w' : World)
    (hl : (snapshot w).slots i = some p.internalId)
    (hr : (setPeer i p).run w = .ok ((), w')) : snapshot w' = snapshot w := by
  cases hr
  apply Store.ext
  · rfl
  · funext j
    cases hd : w.k.wg with
    | none => simp [snapshot, hd]
    | some d =>
      simp only [snapshot, hd, Option.bind_some] at hl
      simp only [snapshot, Option.map_some, hd, Option.bind_some,
        Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq]
      by_cases h : i = j
      · subst j
        simpa only [ite_true, Option.map_some] using hl.symm
      · simp only [if_neg h]

theorem peerGet_retained (i : PeerId) : ProjectedAction snapshot Retained (peerGet i) := by
  apply ProjectedAction.of_wp
  intro s
  mvcgen [peerGet, requireNotPending, getPeer_spec, getDev, getK, setPeer, modifyDev, modifyK,
    branch, branchCmp, refcountInc, unsupported, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try solve | simp_all [snapshot]; exact .refl _
  all_goals obtain ⟨_, _, _, _⟩ := ‹_ ∧ ∃ _, _ ∧ _›
  all_goals try simp_all only
  all_goals try obtain ⟨_, _, _, _⟩ := ‹_ ∧ ∃ _, _ ∧ _›
  all_goals try simp_all [snapshot]
  subst s
  change Retained (mapStore _ _) (mapStore _ _)
  apply mapStore_insert_retained
  · assumption
  · rfl

theorem peerPut_retained (i : Option PeerId) : ProjectedAction snapshot Retained (peerPut i) := by
  apply ProjectedAction.of_wp
  intro s
  mvcgen [peerPut, requireNotPending, getPeer_spec, getDev, getK, setPeer, modifyDev, modifyK,
    branch, branchCmp, refcountDecAndTest, indexRemove, retirePeerUnits, unsupported, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try solve | simp_all [snapshot]; exact .refl _
  all_goals obtain ⟨_, _, _, _⟩ := ‹_ ∧ ∃ _, _ ∧ _›
  all_goals try simp_all only
  all_goals try obtain ⟨_, _, _, _⟩ := ‹_ ∧ ∃ _, _ ∧ _›
  all_goals try simp_all [snapshot]
  all_goals try subst s
  all_goals first
  | exact .refl _
  | exact mapStore_insert_erase _ _ _ _
  | apply mapStore_insert_retained <;> first | assumption | rfl

/-- Only original lookup, reference acquisition and reference release. The
conditional raw-setter theorem above and peer allocation are separate. -/
inductive Primitive : (α : Type) → M α → Prop where
  | lookup (i) : Primitive Peer (getPeer i)
  | acquire (i) : Primitive Unit (peerGet i)
  | release (i) : Primitive Unit (peerPut i)

theorem primitive_contract (h : Primitive α a) :
    Action (fun _ => True) (fun w v => Retained (snapshot w) (snapshot v)) a := by
  intro w x w' _ hr
  refine ⟨True.intro, ?_⟩
  cases h with
  | lookup i =>
    have he := (getPeer_current i w w' x hr).1
    rw [he]
    exact .refl _
  | acquire i => exact peerGet_retained i w x w' hr
  | release i => exact peerPut_retained i w x w' hr

def Sequence := Executions Primitive

theorem sequence_retained (h : Sequence w w') : Retained (snapshot w) (snapshot w') :=
  (h.contract (P := fun _ => True) (R := fun w v => Retained (snapshot w) (snapshot v))
    (fun w => Retained.refl (snapshot w)) (fun _ _ _ => Retained.trans)
    (fun _ hp => primitive_contract hp) True.intro).2

end Leanux.Proofs.WG.Peers
