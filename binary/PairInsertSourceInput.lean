import SourceAdapter
import PairInsertSourceLoop

namespace Binary.Pair.Insert.Source
open Leanux Leanux.WG

/-- The exact input protocol of an accepted insertion: zero or more
collisions, then one fresh value. The table is unchanged between draws. -/
inductive DrawSearch (entries : List IndexEntry) : List HiddenRecord → Nat → List HiddenRecord → Prop
  | fresh {records value rest} : draw records=.ok (value,rest) →
      entries.any (·.index==value)=false → DrawSearch entries records value rest
  | collision {records value next result rest} : draw records=.ok (value,next) →
      entries.any (·.index==value)=true → DrawSearch entries next result rest →
      DrawSearch entries records result rest

theorem RetryPath.supplied {owner w index final} (path : RetryPath owner w index final)
    {d records} (device : w.wg.dev=some d) (input : w.hidden=some records) :
    ∃ rest, DrawSearch d.indexTable records index rest ∧ final.hidden=some rest ∧
      final.wg.dev=some {d with indexTable := ⟨index,owner⟩::d.indexTable} := by
  induction path generalizing d records with
  | @found w index drawn first second final consumed walk locked updated =>
    obtain ⟨rest,decoded,drawFrame⟩ := hidden_draw input consumed
    have drawnDevice : drawn.wg.dev=some d := by rw [drawFrame]; exact device
    obtain ⟨miss,firstFrame⟩ := hasBucket_effect drawnDevice walk
    have firstDevice : first.wg.dev=some d := by rw [firstFrame]; exact drawnDevice
    have secondFrame := (hasBucket_effect firstDevice locked).2
    have secondDevice : second.wg.dev=some d := by rw [secondFrame]; exact firstDevice
    have effect : (Source.modifyDev fun dev => {dev with indexTable := ⟨index,owner⟩::dev.indexTable}).run second=
        .ok ((),{second with wg := {second.wg with dev := some {d with indexTable := ⟨index,owner⟩::d.indexTable}}}) := by
      simp [Binary.Source.modifyDev_run, secondDevice]
    rw [effect] at updated
    have finalEq := (congrArg Prod.snd (Except.ok.inj updated)).symm
    dsimp only at finalEq
    refine ⟨rest,.fresh decoded miss.symm,?_,?_⟩
    · rw [finalEq,secondFrame,firstFrame,drawFrame]
    · rw [finalEq]
  | @collision w value drawn middle index final consumed walk tail ih =>
    obtain ⟨next,decoded,drawFrame⟩ := hidden_draw input consumed
    have drawnDevice : drawn.wg.dev=some d := by rw [drawFrame]; exact device
    obtain ⟨hit,middleFrame⟩ := hasBucket_effect drawnDevice walk
    have middleDevice : middle.wg.dev=some d := by rw [middleFrame]; exact drawnDevice
    have middleInput : middle.hidden=some next := by rw [middleFrame,drawFrame]
    obtain ⟨rest,search,remaining,result⟩ := ih middleDevice middleInput
    exact ⟨rest,.collision decoded hit.symm search,remaining,result⟩

theorem source_input_effect {owner w d index final records}
    (device : w.wg.dev=some d) (input : w.hidden=some records)
    (accepted : (Source.indexInsert owner).run w=.ok (index,final)) :
    ∃ rest,
      DrawSearch (d.indexTable.filter (fun e => !(e.owner==owner))) records index rest ∧
      final.hidden=some rest ∧ final.wg.dev=some {d with
        indexTable := ⟨index,owner⟩::d.indexTable.filter (fun e => !(e.owner==owner))} := by
  have path := source_path device accepted
  have unlinkedDevice : (unlinkedWorld w d owner).wg.dev=some {d with
      indexTable := d.indexTable.filter (fun e => !(e.owner==owner))} := rfl
  have unlinkedInput : (unlinkedWorld w d owner).hidden=some records := input
  exact path.supplied unlinkedDevice unlinkedInput

#print axioms source_input_effect
end Binary.Pair.Insert.Source
