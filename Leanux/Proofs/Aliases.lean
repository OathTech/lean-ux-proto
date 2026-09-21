import Leanux.Reference.AliasContract

namespace Leanux.Proofs

open FS

/-- This proof uses the actual close transition. Its table update is local to
    the closed descriptor and preserves the whole shared object store. -/
theorem close_alias_preservation : Reference.CloseAliasPreservation := by
  intro s closed other a b file _wellFormed distinct closedLookup otherLookup _alias access
  have otherDistinct : other ≠ closed := Ne.symm distinct
  have objectAccess : s.objects b.objectId = some file := by
    simpa [lookupFile, otherLookup] using access
  refine ⟨removeDescriptor s closed, ?_, ?_, ?_, ?_, ?_⟩
  · simp [fileCloseFd, closedLookup]
  · simp [lookupDescriptor, removeDescriptor]
  · simpa [lookupDescriptor, removeDescriptor, otherDistinct] using otherLookup
  · simpa [lookupFile, lookupDescriptor, removeDescriptor, otherDistinct] using access
  · exact objectAccess

theorem initialFiles_wellFormed : WellFormed initialFiles := by
  simp [WellFormed, initialFiles]

/-- Concrete witnesses ensure the alias obligation's admitted domain is
    inhabited, including different descriptor-local close-on-exec flags. -/
def aliasFixtureFile : File := ⟨⟨5, false⟩, 2050⟩

def aliasFixture : Files := {
  fdTable := fun fd =>
    if fd = 8 then some ⟨0, true⟩
    else if fd = 9 then some ⟨0, false⟩ else none
  objects := fun objectId => if objectId = 0 then some aliasFixtureFile else none
  nextObject := 1
  nextFd := 10
  limit := 32 }

theorem aliasFixture_wellFormed : WellFormed aliasFixture := by
  refine ⟨rfl, by decide, by decide, ?_, ?_⟩
  · intro fd d lookup
    by_cases eight : fd = 8
    · subst fd
      simp [aliasFixture] at lookup
      subst d
      exact ⟨by decide, by decide, by decide, aliasFixtureFile, rfl⟩
    · by_cases nine : fd = 9
      · subst fd
        simp [aliasFixture] at lookup
        subst d
        exact ⟨by decide, by decide, by decide, aliasFixtureFile, rfl⟩
      · simp [aliasFixture, eight, nine] at lookup
  · intro fd lower upper
    change fd < 10 at upper
    have cases : fd = 8 ∨ fd = 9 := by omega
    rcases cases with rfl | rfl <;> simp [aliasFixture]

theorem aliasFixture_admitted :
    WellFormed aliasFixture ∧
    (8 : Nat) ≠ 9 ∧
    lookupDescriptor aliasFixture 8 = some ⟨0, true⟩ ∧
    lookupDescriptor aliasFixture 9 = some ⟨0, false⟩ ∧
    lookupFile aliasFixture 9 = some aliasFixtureFile := by
  exact ⟨aliasFixture_wellFormed, by decide, rfl, rfl, rfl⟩

theorem aliasFixture_close_preserves_access :
    ∃ after,
      fileCloseFd aliasFixture 8 = some (⟨0, true⟩, after) ∧
      lookupDescriptor after 8 = none ∧
      lookupDescriptor after 9 = some ⟨0, false⟩ ∧
      lookupFile after 9 = some aliasFixtureFile ∧
      after.objects 0 = some aliasFixtureFile := by
  exact close_alias_preservation aliasFixture 8 9 ⟨0, true⟩ ⟨0, false⟩
    aliasFixtureFile aliasFixture_wellFormed (by decide) rfl rfl rfl rfl

end Leanux.Proofs
