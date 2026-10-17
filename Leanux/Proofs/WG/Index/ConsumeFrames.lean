import Leanux.Proofs.WG.Index.Lookup
import Leanux.Proofs.WG.Index.PeerWords
import Leanux.Proofs.WG.Index.SendFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

/-! Lookup changes references and embedded peer words, including the NULL
store after a failed get. Its table and allocation cursor remain unchanged.
These frames do not assert owner residency or peer-word coherence. -/
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do
open TimerDiscipline (TableCursor tableCursor)

theorem peerGetMaybeZero_cursor (peer : Option PeerId) (cursor : Option TableCursor) :
    ⦃fun w => ⌜w.k.wg.map tableCursor = cursor⌝⦄ peerGetMaybeZero peer
      ⦃⇓? _ w => ⌜w.k.wg.map tableCursor = cursor⌝⦄ := by
  have hr := refcountIncNotZero_kernel_variant (fun k => k.wg.map tableCursor = cursor)
  mvcgen [peerGetMaybeZero, requireNotPending, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, invariant, hr]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [tableCursor, Option.map_map, Function.comp_def]
  all_goals assumption

theorem lookupFinish_cursor (state : LookupState) (cursor : Option TableCursor) :
    ⦃fun w => ⌜w.k.wg.map tableCursor = cursor⌝⦄ lookupFinish state
      ⦃⇓? _ w => ⌜w.k.wg.map tableCursor = cursor⌝⦄ := by
  have hg := fun peer => peerGetMaybeZero_cursor peer cursor
  obtain ⟨entry, stopped⟩ := state
  cases entry with
  | none => mvcgen [lookupFinish, branch, invariant]
  | some entry =>
    obtain ⟨index, owner⟩ := entry
    cases owner <;>
      mvcgen [lookupFinish, IndexOwner.peerWord, IndexOwner.setPeerWord,
        getPeer, getKeypair, getDev, getK, setPeer, setKeypair,
        modifyDev, modifyK, branch, invariant, hg]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [tableCursor, Option.map_map, Function.comp_def]

/-- The existing scan is reused unchanged. Its complete-device result feeds
the same original lookup suffix, including every dead/NULL storeback. -/
theorem indexLookup_cursor (kinds : List IndexKind) (index : Nat) (cursor : Option TableCursor) :
    Ensures (indexLookup kinds index) (fun w => w.k.wg.map tableCursor = cursor)
      (fun _ w => w.k.wg.map tableCursor = cursor) := by
  intro w result final pre run
  cases hd : w.k.wg with
  | none =>
    have stop : getDev.run w = .error (.invariant "no WireGuard device in this trace's fixture") := by
      simp [getDev, getK, invariant, hd, StateT.run_bind]
      rfl
    rw [indexLookup_factor] at run
    simp only [lookupPrefix, indexBucket, bind_assoc, pure_bind] at run
    change (getDev.run w >>= _) = _ at run
    rw [stop] at run
    cases run
  | some d =>
    obtain ⟨state, middle, execution, selected, device⟩ := lookupPrefix_returns kinds index d w hd
    rw [indexLookup_factor, StateT.run_bind, execution] at run
    exact (ensures_iff _ _ _).mpr (lookupFinish_cursor state cursor)
      middle result final (by simpa [device, hd] using pre) run

theorem pubkeyLookup_cursor (key : Key) (cursor : Option TableCursor) :
    ⦃fun w => ⌜w.k.wg.map tableCursor = cursor⌝⦄ pubkeyLookup key
      ⦃⇓? _ w => ⌜w.k.wg.map tableCursor = cursor⌝⦄ := by
  have hg := fun peer => peerGetMaybeZero_cursor peer cursor
  mvcgen [pubkeyLookup, getDev, getK, branch, invariant, hg]

theorem indexLookup_tables (kinds : List IndexKind) (index : Nat) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ indexLookup kinds index
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  exact tablesSafe_of_cursor w.k final.k
    (indexLookup_cursor kinds index (w.k.wg.map tableCursor) w result final rfl run) pre

theorem pubkeyLookup_tables (key : Key) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ pubkeyLookup key
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro w result final pre run
  exact tablesSafe_of_cursor w.k final.k
    ((ensures_iff _ _ _).mpr (pubkeyLookup_cursor key (w.k.wg.map tableCursor))
      w result final rfl run) pre

end Leanux.Proofs.WG.Index
