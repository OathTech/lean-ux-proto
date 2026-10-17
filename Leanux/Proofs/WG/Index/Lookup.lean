import Leanux.Proofs.WG.Index.LookupPrefixSource
import Leanux.Proofs.WG.Noise.AccessSource
import Leanux.Proofs.WG.Noise.ComponentFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

def tableAt (g : WGWorld) : Option (List IndexEntry) := g.dev.map Device.indexTable

theorem lookupFinish_owner (entry : Option IndexEntry) (stopped : Bool)
    (table : List IndexEntry) :
    Ensures (lookupFinish (entry, stopped)) (fun g => tableAt g = some table)
      (fun result g => tableAt g = some table ∧
        ∀ owner pid, result = some (owner, pid) → ∃ e, entry = some e ∧ e.owner = owner) := by
  let P : WGWorld → Prop := fun g => tableAt g = some table
  let R : Option (IndexOwner × PeerId) → WGWorld → Prop := fun result g =>
    P g ∧ ∀ owner pid, result = some (owner, pid) → ∃ e, entry = some e ∧ e.owner = owner
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g ambient y g' ambient' hp hr
    cases hr
    exact hp
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hget (pid : PeerId) : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient p g' ambient' hp hr
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P) g ambient p g' ambient' hp hr).1
  have hkey (kp : KeypairId) : Ensures (getKeypair kp) P (fun _ => P) := by
    intro g ambient k g' ambient' hp hr
    cases hd : g.dev with
    | none =>
      simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hk : d.keypairs[kp]? with
      | none =>
        simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
        cases hr
      | some k =>
        simp [getKeypair, getDev, hd, hk] at hr
        rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        exact hp
  have hmodify (f : Device → Device) (hf : ∀ d, (f d).indexTable = d.indexTable) :
      Ensures (modifyDev f) P (fun _ => P) := by
    intro g ambient result g' ambient' hp hr
    change Except.ok (((), {g with dev := g.dev.map f}), ambient) = _ at hr
    cases hr
    change (g.dev.map f).map Device.indexTable = some table
    rw [Option.map_map]
    simpa only [P, tableAt, Function.comp_def, hf] using hp
  have hword (owner : IndexOwner) : Ensures owner.peerWord P (fun _ => P) := by
    cases owner with
    | handshake pid =>
      exact ensures_bind _ _ (hget pid) (fun p => hpure p.handshakeEntryPeer)
    | keypair kp =>
      exact ensures_bind _ _ (hkey kp) (fun k => hpure k.peer)
  have hstore (owner : IndexOwner) (word : Option PeerId) :
      Ensures (owner.setPeerWord word) P (fun _ => P) := by
    cases owner with
    | handshake pid =>
      exact ensures_bind _ _ (hget pid) (fun p => hmodify _ (fun _ => rfl))
    | keypair kp =>
      exact ensures_bind _ _ (hkey kp) (fun k => hmodify _ (fun _ => rfl))
  have href (old : Nat) : Ensures (refcountIncNotZero old : WG.M Bool) P (fun _ => P) := by
    intro g ambient result g' ambient' hp hr
    by_cases zero : old = 0
    · subst old
      simp [refcountIncNotZero, branchCmp, AmbientM.branchCmp,
        branch, AmbientM.branch] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact hp
    · by_cases overflow : old + 1 ≥ 2 ^ 31
      · simp [refcountIncNotZero, branchCmp, AmbientM.branchCmp,
          branch, AmbientM.branch, zero, overflow, unsupported, AmbientM.unsupported] at hr
        cases hr
      · simp [refcountIncNotZero, branchCmp, AmbientM.branchCmp,
          branch, AmbientM.branch, zero, overflow] at hr
        rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        exact hp
  have hpeer (word : Option PeerId) : Ensures (peerGetMaybeZero word) P (fun _ => P) := by
    unfold peerGetMaybeZero
    refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
    intro null
    cases null with
    | true => exact hpure none
    | false =>
      cases word with
      | none =>
        exact (ensures_iff _ _ _).mpr
          (hoare_liftAmbient_variant (AmbientM.invariant "unreachable") P)
      | some pid =>
        simp only [requireNotPending, pure_bind]
        refine ensures_bind (Q := fun _ => P) _ _ (hget pid) ?_
        intro p
        refine ensures_bind (Q := fun _ => P) _ _ (href p.refcount) ?_
        intro live
        refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
        intro dead
        cases dead with
        | true => exact hpure none
        | false =>
          exact ensures_bind _ _ (hmodify _ (fun _ => rfl)) (fun _ => hpure (some pid))
  have hreturn (value : Option (IndexOwner × PeerId))
      (origin : ∀ owner pid, value = some (owner, pid) →
        ∃ e, entry = some e ∧ e.owner = owner) :
      Ensures (pure value : WG.M (Option (IndexOwner × PeerId))) P R := by
    intro g ambient result g' ambient' hp hr
    cases hr
    exact ⟨hp, origin⟩
  have hstop : Ensures (invariant "unreachable" : WG.M (Option (IndexOwner × PeerId))) P R := by
    intro g ambient result g' ambient' hp hr
    simp [invariant, AmbientM.invariant] at hr
    cases hr
  have htail : Ensures (lookupFinish (entry, true)) P R := by
    unfold lookupFinish
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
    intro found
    cases found with
    | false => exact hreturn none (by simp)
    | true =>
      cases entry with
      | none => exact hstop
      | some e =>
        refine ensures_bind (Q := fun _ => P) _ _ (hword e.owner) ?_
        intro word
        refine ensures_bind (Q := fun _ => P) _ _ (hpeer word) ?_
        intro peer
        refine ensures_bind (Q := fun _ => P) _ _ (hstore e.owner peer) ?_
        intro _
        refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
        intro alive
        cases alive with
        | false => exact hreturn none (by simp)
        | true =>
          cases peer with
          | none => exact hstop
          | some pid =>
            exact hreturn (some (e.owner, pid)) (by
              intro owner id returned
              simp only [Option.some.injEq, Prod.mk.injEq] at returned
              exact ⟨e, rfl, returned.1⟩)
  change Ensures _ P R
  cases stopped with
  | true => exact htail
  | false =>
    unfold lookupFinish
    simp only [Bool.not_false, ↓reduceIte]
    exact ensures_bind _ _ (hbranch _ _) (fun _ => htail)

/-- Normal lookup returns only an owner of an initial row at the requested
index and permitted kind, and leaves the index table unchanged. -/
theorem indexLookup_owner (kinds : List IndexKind) (index : Nat) (d : Device) :
    Ensures (indexLookup kinds index) (fun g => g.dev = some d)
      (fun result g => tableAt g = some d.indexTable ∧
        ∀ owner pid, result = some (owner, pid) →
          ∃ e ∈ d.indexTable, e.index = index ∧ e.owner = owner ∧ kinds.contains e.kind = true) := by
  intro g ambient result final after device run
  obtain ⟨state, middle, next, hprefix, selected, device'⟩ :=
    lookupPrefix_returns kinds index d g ambient device
  rw [indexLookup_factor] at run
  change (((lookupPrefix kinds index).run g).run ambient >>= fun ((s, m), a) =>
    ((lookupFinish s).run m).run a) = _ at run
  rw [hprefix] at run
  have h := lookupFinish_owner state.1 state.2 d.indexTable middle next result final after
    (by simp [tableAt, device']) run
  refine ⟨h.1, ?_⟩
  intro owner pid returned
  obtain ⟨e, entry, owned⟩ := h.2 owner pid returned
  rw [selected] at entry
  obtain ⟨member, numeric, permitted⟩ := selectedState_origin kinds index _ e entry
  exact ⟨e, (List.mem_filter.mp member).1, numeric, owned, permitted⟩

end Leanux.Proofs.WG.Index
