import Leanux.Proofs.Framing.WP
import Leanux.Proofs.WG.Lifetimes.Actions
import Leanux.Proofs.Framing.Lift
import Leanux.WG.Peer

set_option pp.structureInstances false
set_option maxHeartbeats 800000

/-! Peer allocation identities for the current store. A raw slot reference is
not an ownership proof: in particular the dump-cursor counterexample can select
a newly allocated peer. These helpers prove only the identities they retain. -/
namespace Leanux.Proofs.WG.Peers
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Lifetimes Leanux.Proofs.Framing

def mapStore (frontier : Nat) (peers : Std.TreeMap Nat Peer) : Store PeerId :=
  ⟨frontier, fun i => peers[i]?.map (·.internalId)⟩

def snapshot (w : WGWorld) : Store PeerId :=
  ⟨w.peerCounter, fun i => (w.dev.bind fun d => d.peers[i]?).map (·.internalId)⟩

theorem getPeer_current (i : PeerId) (w w' : WGWorld) (p : Peer)
    (ambient ambient' : Ambient)
    (hr : ((getPeer i).run w).run ambient = .ok ((p, w'), ambient')) :
    w' = w ∧ ambient' = ambient ∧ (snapshot w).slots i = some p.internalId := by
  cases hd : w.dev with
  | none =>
    simp [getPeer, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hp : d.peers[i]? with
    | none =>
      simp [getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some old =>
      have he : ((getPeer i).run w).run ambient = .ok ((old, w), ambient) := by
        simp [getPeer, getDev, hd, hp] <;> rfl
      rw [he] at hr
      cases hr
      exact ⟨rfl, rfl, by simp [snapshot, hd, hp]⟩

theorem getPeer_spec (i : PeerId) (start : WGWorld) (initialAmbient : Ambient) :
    ⦃fun w ambient => ⌜w = start ∧ ambient = initialAmbient⌝⦄ getPeer i
    ⦃⇓? p w ambient => ⌜w = start ∧ ambient = initialAmbient ∧
      ∃ d, w.dev = some d ∧ d.peers[i]? = some p⌝⦄ := by
  intro w
  change Hoare ((getPeer i).run w)
    (fun ambient => w = start ∧ ambient = initialAmbient)
    (fun out ambient => out.2 = start ∧ ambient = initialAmbient ∧
      ∃ d, out.2.dev = some d ∧ d.peers[i]? = some out.1)
  apply (hoare_iff_run _ _ _).mpr
  rintro ambient ⟨p, w'⟩ ambient' hq hr
  cases hd : w.dev with
  | none =>
    simp [getPeer, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hp : d.peers[i]? with
    | none =>
      simp [getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some old =>
      have he : ((getPeer i).run w).run ambient = .ok ((old, w), ambient) := by
        simp [getPeer, getDev, hd, hp] <;> rfl
      rw [he] at hr
      cases hr
      exact ⟨hq.1, hq.2, d, hd, hp⟩

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
theorem setPeer_same (i : PeerId) (p : Peer) (w w' : WGWorld)
    (ambient ambient' : Ambient)
    (hl : (snapshot w).slots i = some p.internalId)
    (hr : ((setPeer i p).run w).run ambient = .ok (((), w'), ambient')) :
    snapshot w' = snapshot w := by
  cases hr
  apply Store.ext
  · rfl
  · funext j
    cases hd : w.dev with
    | none => simp [snapshot, hd]
    | some d =>
      simp only [snapshot, hd, Option.bind_some] at hl
      simp only [snapshot, Option.map_some, hd, Option.bind_some,
        Std.TreeMap.getElem?_insert, Std.LawfulEqOrd.compare_eq_iff_eq]
      by_cases h : i = j
      · subst j
        simpa only [ite_true, Option.map_some] using hl.symm
      · simp only [ite_eq_right h]

theorem peerGet_retained (i : PeerId) : ProjectedAction snapshot Retained (peerGet i) := by
  apply ProjectedAction.of_wp
  intro s
  mvcgen [peerGet, requireNotPending, getPeer, getDev, setPeer, modifyDev,
    branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, refcountInc,
    unsupported, invariant, AmbientM.unsupported, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try solve | simp_all [snapshot]; exact .refl _
  all_goals try simp_all [snapshot]
  subst s
  change Retained (mapStore _ _) (mapStore _ _)
  apply mapStore_insert_retained
  · assumption
  · rfl

theorem peerPut_retained (i : Option PeerId) : ProjectedAction snapshot Retained (peerPut i) := by
  apply ProjectedAction.of_wp
  intro s
  have unhash (a : IndexM Unit) (g : WGWorld) : Hoare (MonadLift.monadLift a : WG.M Unit)
      (fun w => w = g)
      (fun _ w => ∃ table, w = {g with dev := g.dev.map fun d => {d with indexTable := table}}) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x w' ambient' hw hr
    subst w
    change ((liftIndex a).run g).run ambient = .ok ((x, w'), ambient') at hr
    rw [liftIndex_run] at hr
    cases hg : g.dev with
    | none => simp [hg] at hr
    | some d =>
      simp only [hg] at hr
      cases ha : (a.run d.indexTable).run ambient with
      | error e => simp [ha, Except.map] at hr
      | ok out =>
        rcases out with ⟨⟨y, table⟩, ambient''⟩
        simp only [ha, Except.map, Except.ok.injEq, Prod.mk.injEq] at hr
        rcases hr with ⟨⟨_, hw⟩, _⟩
        exact ⟨table, by simpa [hg] using hw.symm⟩
  unfold Hoare at unhash
  mvcgen [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
    branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    refcountDecAndTest, unhash, retirePeerUnits, modifyAmbient,
    unsupported, invariant, AmbientM.unsupported, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try obtain ⟨table, rfl⟩ := ‹∃ table, _ = _›
  all_goals try simp_all [snapshot]
  all_goals subst_vars
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [Function.comp_def]
  all_goals try subst s
  all_goals first
  | exact .refl _
  | exact mapStore_insert_erase _ _ _ _
  | apply mapStore_insert_retained <;> first | assumption | rfl

/-- Only original lookup, reference acquisition and reference release. The
conditional raw-setter theorem above and peer allocation are separate. -/
inductive Primitive : (α : Type) → WG.M α → Prop where
  | lookup (i) : Primitive Peer (getPeer i)
  | acquire (i) : Primitive Unit (peerGet i)
  | release (i) : Primitive Unit (peerPut i)

theorem primitive_contract (h : Primitive α a) :
    Action (fun _ => True) (fun w v => Retained (snapshot w) (snapshot v)) a := by
  apply (Action.iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' _ hr
  refine ⟨True.intro, ?_⟩
  cases h with
  | lookup i =>
    have he := (getPeer_current i w w' x ambient ambient' hr).1
    rw [he]
    exact .refl _
  | acquire i =>
    exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (peerGet_retained i) w ambient x w' ambient' hr
  | release i =>
    exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (peerPut_retained i) w ambient x w' ambient' hr

def Sequence := Executions Primitive

theorem sequence_retained (h : Sequence w ambient w' ambient') :
    Retained (snapshot w) (snapshot w') :=
  (h.contract (P := fun _ => True) (R := fun w v => Retained (snapshot w) (snapshot v))
    (fun w => Retained.refl (snapshot w)) (fun _ _ _ => Retained.trans)
    (fun _ hp => primitive_contract hp) True.intro).2

end Leanux.Proofs.WG.Peers
