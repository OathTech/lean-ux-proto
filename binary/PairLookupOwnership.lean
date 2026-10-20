import PairLookupReconstruct

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG Index

theorem SourceFrame.targetOwnership {c before after} (source : SourceFrame c before after) :
    Remove.targetOwnership after=Remove.targetOwnership before := by
  have keys := source.owner_keys
  have keyform (d : Device) : Remove.targetOwnership d=
      ((target d).ownerWords.map Prod.fst).map (fun owner => (owner,d.indexTable.any (·.owner==owner))) := by
    simp only [Remove.targetOwnership,target,Id.run,Pure.pure,List.map_append,List.map_map,Function.comp_def]
  rw [keyform after,keyform before,keys,source.table]

theorem SpansFrame.ownership {n o before after} (frame : SpansFrame (shapeSpans n o) before after)
    (layout : Layout o) : Remove.ownership n o before=Remove.ownership n o after := by
  apply Trie.mapM_same
  rintro ⟨owner,base⟩ named
  have member : (base+8,24) ∈ shapeSpans n o :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(owner,base),named,rfl⟩)
  have same := frame.word member 8 8 (by omega) "owner.pprev"
  dsimp only at same ⊢
  simp only [layout.hash,layout.pprev,same]

theorem ownership_after {n o coverage s w d query kinds ra after finalDevice}
    (facts : CallFacts n o coverage s w d query kinds ra)
    (source : SourceFrame (callConfig n w d query kinds) d finalDevice)
    (frame : EqualOutside (LookupRelation.LookupWrites (callConfig n w d query kinds) coverage.coverage coverage.preempt s.data
      (callView (callConfig n w d query kinds) d)) s.data.dmem after) :
    Remove.ownership n o after=.ok (Remove.targetOwnership finalDevice) := by
  have same := (facts.shape_frame frame).ownership (validate_basic (reconstruct_components facts.related).1).1
  rw [←same,source.targetOwnership]
  exact facts.owners

#print axioms ownership_after
end Binary.Pair.IndexLookup
