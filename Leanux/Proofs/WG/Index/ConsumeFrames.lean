import Leanux.Proofs.WG.Index.Lookup
import Leanux.Proofs.WG.Index.PeerWords
import Leanux.Proofs.WG.Index.SendFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do
open TimerDiscipline (TableCursor tableCursor)

theorem peerGetMaybeZero_cursor (peer : Option PeerId) (cursor : Option TableCursor) :
    ⦃fun g => ⌜g.dev.map tableCursor = cursor⌝⦄ peerGetMaybeZero peer
      ⦃⇓? _ g => ⌜g.dev.map tableCursor = cursor⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases peer with
  | none =>
    simp [peerGetMaybeZero, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact pre
  | some pid =>
    cases device : g.dev with
    | none =>
      simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, device,
        branch, AmbientM.branch, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.peers[pid]? with
      | none =>
        simp [peerGetMaybeZero, requireNotPending, getPeer, getDev, device, resident,
          branch, AmbientM.branch, invariant, AmbientM.invariant] at run
        cases run
      | some p =>
        by_cases zero : p.refcount = 0
        · simp [peerGetMaybeZero, requireNotPending, refcountIncNotZero,
            getDev, device, getPeer, resident, zero, branch, branchCmp,
            AmbientM.branch, AmbientM.branchCmp] at run
          rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
          exact pre
        · by_cases overflow : 2147483647 ≤ p.refcount
          · simp [peerGetMaybeZero, requireNotPending, refcountIncNotZero,
              getDev, device, getPeer, resident, zero, overflow, branch, branchCmp,
              AmbientM.branch, AmbientM.branchCmp, unsupported, AmbientM.unsupported] at run
            cases run
          · simp [peerGetMaybeZero, requireNotPending, refcountIncNotZero,
              getDev, device, getPeer, resident, zero, overflow, branch, branchCmp,
              AmbientM.branch, AmbientM.branchCmp, setPeer, modifyDev] at run
            rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
            simpa [device, tableCursor] using pre

theorem lookupFinish_cursor (state : LookupState) (cursor : Option TableCursor) :
    ⦃fun g => ⌜g.dev.map tableCursor = cursor⌝⦄ lookupFinish state
      ⦃⇓? _ g => ⌜g.dev.map tableCursor = cursor⌝⦄ := by
  let P : WGWorld → Prop := fun g => g.dev.map tableCursor = cursor
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hstop {α : Type} (message : String) : Ensures (invariant message : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
  have hget (pid : PeerId) : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P) g ambient result final after pre run).1
  have hkey (kid : KeypairId) : Ensures (getKeypair kid) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none =>
      simp [getKeypair, getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases found : d.keypairs[kid]? with
      | none =>
        simp [getKeypair, getDev, device, found, invariant, AmbientM.invariant] at run
        cases run
      | some k =>
        simp [getKeypair, getDev, device, found] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        exact pre
  have hmodify (f : Device → Device) (stable : ∀ d, tableCursor (f d) = tableCursor d) :
      Ensures (modifyDev f) P (fun _ => P) := by
    intro g ambient result final after pre run
    change Except.ok (((), {g with dev := g.dev.map f}), ambient) = _ at run
    cases run
    simpa only [P, Option.map_map, Function.comp_def, stable] using pre
  have hword (owner : IndexOwner) : Ensures owner.peerWord P (fun _ => P) := by
    cases owner with
    | handshake pid => exact ensures_bind _ _ (hget pid) (fun p => hpure p.handshakeEntryPeer)
    | keypair kid => exact ensures_bind _ _ (hkey kid) (fun k => hpure k.peer)
  have hstore (owner : IndexOwner) (word : Option PeerId) :
      Ensures (owner.setPeerWord word) P (fun _ => P) := by
    cases owner with
    | handshake pid => exact ensures_bind _ _ (hget pid) (fun p => hmodify _ (fun _ => rfl))
    | keypair kid => exact ensures_bind _ _ (hkey kid) (fun k => hmodify _ (fun _ => rfl))
  have hpeer (word : Option PeerId) : Ensures (peerGetMaybeZero word) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (peerGetMaybeZero_cursor word cursor)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (left : Ensures yes P (fun _ => P)) (right : Ensures no P (fun _ => P)) :
      Ensures (if condition then yes else no) P (fun _ => P) := by
    split <;> assumption
  apply (ensures_iff _ _ _).mp
  change Ensures _ P (fun _ => P)
  obtain ⟨entry, stopped⟩ := state
  unfold lookupFinish
  cases stopped <;> cases entry
  all_goals simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
  all_goals repeat' first
    | exact hpure _
    | exact hbranch _ _
    | exact hstop _
    | exact hword _
    | exact hstore _ _
    | exact hpeer _
    | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (refine hif _ _ _ ?_ ?_)
    | (split)

theorem indexLookup_cursor (kinds : List IndexKind) (index : Nat) (cursor : Option TableCursor) :
    Ensures (indexLookup kinds index) (fun g => g.dev.map tableCursor = cursor)
      (fun _ g => g.dev.map tableCursor = cursor) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    rw [indexLookup_factor] at run
    simp [lookupPrefix, liftIndex, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    obtain ⟨state, middle, next, execution, selected, present⟩ :=
      lookupPrefix_returns kinds index d g ambient device
    rw [indexLookup_factor] at run
    change (((lookupPrefix kinds index).run g).run ambient >>= fun ((s, m), a) =>
      ((lookupFinish s).run m).run a) = _ at run
    rw [execution] at run
    exact (ensures_iff _ _ _).mpr (lookupFinish_cursor state cursor)
      middle next result final after (by simpa [present, device] using pre) run

theorem pubkeyLookup_cursor (key : Key) (cursor : Option TableCursor) :
    ⦃fun g => ⌜g.dev.map tableCursor = cursor⌝⦄ pubkeyLookup key
      ⦃⇓? _ g => ⌜g.dev.map tableCursor = cursor⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  let P : WGWorld → Prop := fun g => g.dev.map tableCursor = cursor
  have hread : Ensures getDev P (fun _ => P) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  unfold pubkeyLookup
  refine ensures_bind _ _ hread ?_
  intro d
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (AmbientM.branch .pubkeyLookupMatch _) P)) ?_
  intro _
  exact (ensures_iff _ _ _).mpr (peerGetMaybeZero_cursor _ cursor)

theorem indexLookup_tables (kinds : List IndexKind) (index : Nat) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ indexLookup kinds index
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  exact tablesSafe_of_cursor g final
    (indexLookup_cursor kinds index (g.dev.map tableCursor) g ambient result final after rfl run) pre

theorem pubkeyLookup_tables (key : Key) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ pubkeyLookup key
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  exact tablesSafe_of_cursor g final
    ((ensures_iff _ _ _).mpr (pubkeyLookup_cursor key (g.dev.map tableCursor))
      g ambient result final after rfl run) pre

end Leanux.Proofs.WG.Index
