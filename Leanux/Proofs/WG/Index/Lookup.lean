import Leanux.Proofs.WG.Noise.Slots
import Leanux.Proofs.WG.Index.LookupSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

def tableAt (w : World) : Option (List IndexEntry) := w.k.wg.map Device.indexTable

theorem lookupFinish_owner (entry : Option IndexEntry) (stopped : Bool)
    (table : List IndexEntry) :
    Ensures (lookupFinish (entry, stopped)) (fun w => tableAt w = some table)
      (fun result w => tableAt w = some table ∧
        ∀ owner pid, result = some (owner, pid) → ∃ e, entry = some e ∧ e.owner = owner) := by
  rw [ensures_iff]
  cases entry with
  | none =>
    mvcgen [lookupFinish, branch, invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [tableAt]
  | some e =>
    obtain ⟨index, owner⟩ := e
    cases owner <;>
      mvcgen [lookupFinish, IndexOwner.peerWord, IndexOwner.setPeerWord,
        peerGetMaybeZero, requireNotPending, refcountIncNotZero, getPeer, getKeypair,
        getDev, getK, setPeer, setKeypair, modifyDev, modifyK,
        branch, branchCmp, invariant, unsupported]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [tableAt, Option.map_map, Function.comp_def]
    all_goals grind

def lookupPrefix (kinds : List IndexKind) (index : Nat) : M LookupState := do
  let entries ← indexBucket index
  forIn entries (none, false) (lookupStep kinds index)

theorem indexLookup_factor (kinds : List IndexKind) (index : Nat) :
    indexLookup kinds index = (do
      let state ← lookupPrefix kinds index
      lookupFinish state) := by
  rw [indexLookup_source]
  simp [lookupPrefix, bind_assoc]

def bucket (index : Nat) (table : List IndexEntry) : List IndexEntry :=
  table.filter (·.index % (2 ^ INDEX_HASHTABLE_BITS) == index % (2 ^ INDEX_HASHTABLE_BITS))

theorem lookupPrefix_returns (kinds : List IndexKind) (index : Nat) (d : Device) :
    Returns (lookupPrefix kinds index) (fun w => w.k.wg = some d)
      (fun result w => result = selectedState kinds index (bucket index d.indexTable) (none, false) ∧
        w.k.wg = some d) := by
  have hg : Returns (indexBucket index) (fun w => w.k.wg = some d)
      (fun entries w => entries = bucket index d.indexTable ∧ w.k.wg = some d) := by
    rw [returns_iff]
    mvcgen [indexBucket, getDev, getK, invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [bucket]
  unfold lookupPrefix
  apply returns_bind _ _ hg
  intro entries w pre
  obtain ⟨he, hd⟩ := pre
  subst entries
  obtain ⟨result, final, run, selected, kernel⟩ :=
    lookupScan_returns kinds index (bucket index d.indexTable) (none, false) w.k w rfl
  exact ⟨result, final, run, selected, by rw [kernel]; exact hd⟩

theorem selectedState_origin (kinds : List IndexKind) (index : Nat)
    (entries : List IndexEntry) (e : IndexEntry)
    (selected : (selectedState kinds index entries (none, false)).1 = some e) :
    e ∈ entries ∧ e.index = index ∧ kinds.contains e.kind = true := by
  unfold selectedState at selected
  cases found : entries.find? (·.index == index) with
  | none => simp [found] at selected
  | some entry =>
    simp only [found] at selected
    split at selected
    · simp only [Option.some.injEq] at selected
      subst e
      exact ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found, by assumption⟩
    · simp at selected

/-- Normal lookup returns only an owner of an initial row at the requested
index and permitted kind, and leaves the index table unchanged. -/
theorem indexLookup_owner (kinds : List IndexKind) (index : Nat) (d : Device) :
    Ensures (indexLookup kinds index) (fun w => w.k.wg = some d)
      (fun result w => tableAt w = some d.indexTable ∧
        ∀ owner pid, result = some (owner, pid) →
          ∃ e ∈ d.indexTable, e.index = index ∧ e.owner = owner ∧ kinds.contains e.kind = true) := by
  intro w result final device run
  obtain ⟨state, middle, hprefix, selected, device'⟩ := lookupPrefix_returns kinds index d w device
  rw [indexLookup_factor, StateT.run_bind, hprefix] at run
  have h := lookupFinish_owner state.1 state.2 d.indexTable middle result final
    (by simp [tableAt, device']) run
  refine ⟨h.1, ?_⟩
  intro owner pid returned
  obtain ⟨e, entry, owned⟩ := h.2 owner pid returned
  rw [selected] at entry
  obtain ⟨member, numeric, permitted⟩ := selectedState_origin kinds index _ e entry
  exact ⟨e, (List.mem_filter.mp member).1, numeric, owned, permitted⟩

end Leanux.Proofs.WG.Index
