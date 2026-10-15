import LookupAcceptedSource

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase

/-- A lookup with no selected owner is exactly the logged bucket search
    followed by its outer RET, including first-match wrong-kind termination. -/
theorem lookup_no_owner_source (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (returnAddress : UInt64) (s : MachineState) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress s world v)
    (focused : c.focus.owner = none) :
    ((MirrorHistory.lookup c.kinds c.query).run []).run world =
      .ok ((none, (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).1.2 ++
        [⟨.returned "wg_index_hashtable_lookup", (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).2⟩]),
        (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).2) := by
  obtain ⟨device, hasDevice⟩ : ∃ device, world.k.wg = some device := by
    cases hd : world.k.wg with
    | none => have h := entry.projected; simp [project, hd] at h
    | some device => exact ⟨device, rfl⟩
  have bucketEq : v.bucket = device.indexTable.filter (fun e => e.index % 8192 == c.query % 8192) := by
    have h := congrArg (fun view : Option View => view.map (·.bucket)) entry.projected
    simpa [project, hasDevice] using h.symm
  have selection := (search_selected c v.bucket [sourceEntry world] world).trans (entry.focus.1.trans focused)
  have absent : (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).1.1 = none := by
    cases found : (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).1.1 with
    | none => rfl
    | some chosen => simp [found] at selection
  rw [LookupSearch.lookup_split]
  apply MirrorHistory.called_run_at
  simp only [List.nil_append, StateT.run_bind, StateT.run_lift, StateT.run_pure,
    LookupMirror.bucket_run c.query world device hasDevice]
  rw [← bucketEq]
  change ((do
    let found ← LookupSearch.searchPrefix c.kinds c.query v.bucket
    LookupSearch.searchSuffix found).run [sourceEntry world]).run world = _
  simp only [StateT.run_bind, LookupSearch.prefix_run]
  change ((LookupSearch.searchSuffix (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).1.1).run _).run _ = _
  rw [absent]
  rfl

/-- Determinism connects the exact no-owner source prefix to any supplied
    accepted mirror result; it does not replace the accepted-run premise. -/
theorem lookup_no_owner_accepted (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (returnAddress : UInt64) (s : MachineState) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress s world v)
    (focused : c.focus.owner = none)
    (answer : Option (IndexOwner × PeerId)) (final : World)
    (accepted : (indexLookup c.kinds c.query).run world = .ok (answer, final)) :
    answer = none ∧ final = (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).2 := by
  have logged := lookup_no_owner_source c coverage preempt returnAddress s world v entry focused
  have erased := MirrorHistory.lookup_erases c.kinds c.query [] world
  rw [logged, accepted] at erased
  exact ⟨(congrArg Prod.fst (Except.ok.inj erased)).symm,
    (congrArg Prod.snd (Except.ok.inj erased)).symm⟩

#print axioms lookup_no_owner_source
#print axioms lookup_no_owner_accepted
end Binary.LookupRelation
