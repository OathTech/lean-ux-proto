import Leanux.Proofs.WG.Index.OwnerWordModel

/-! Disjoint reasons for a normally returned empty index lookup. The NULL case
retains the original same-value owner-word write, including map representation. -/
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

inductive LookupNoneCause where
  | absentOrDisallowed
  | nullOwnerWord
  | zeroReference
  deriving DecidableEq

def LookupNoneCase (kinds : List IndexKind) (index : Nat) (d final : Device) :
    LookupNoneCause → Prop
  | .absentOrDisallowed =>
      (∀ e, d.indexTable.find? (·.index == index) = some e →
        kinds.contains e.kind = false) ∧ final = d
  | .nullOwnerWord => ∃ owner,
      d.indexTable.find? (·.index == index) = some { index, owner } ∧
      kinds.contains (IndexEntry.kind { index, owner }) = true ∧
      ownerWord d owner = some none ∧ final = writeOwnerWord d owner none
  | .zeroReference => ∃ owner pid p,
      d.indexTable.find? (·.index == index) = some { index, owner } ∧
      kinds.contains (IndexEntry.kind { index, owner }) = true ∧
      ownerWord d owner = some (some pid) ∧ d.peers[pid]? = some p ∧
      p.refcount = 0 ∧ final = writeOwnerWord d owner none

theorem lookupNoneCase_unique (kinds : List IndexKind) (index : Nat) (d final : Device)
    (a b : LookupNoneCause) (ha : LookupNoneCase kinds index d final a)
    (hb : LookupNoneCase kinds index d final b) : a = b := by
  cases a <;> cases b <;> simp_all [LookupNoneCase]
  all_goals grind

end Leanux.Proofs.WG.Index
