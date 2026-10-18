import PairReplace
import PairBucketReplace

namespace Binary.Pair.Replace
open Leanux Leanux.WG Index

def sourceAnswer (d : Device) (pid : PeerId) : Bool := d.indexTable.any (·.owner==.handshake pid)

def sourceFinal (w : World) (d : Device) (pid : PeerId) (kid : KeypairId) : World :=
  {w with
    k := {w.k with wg := some (if sourceAnswer d pid then
      {d with indexTable := d.indexTable.map (replaceOwner (.handshake pid) (.keypair kid))} else d)}
    steps := w.steps.push {decision := .idxReplaceUnhashed,outcome := !sourceAnswer d pid,netRx := w.netRxSection}}

theorem source_run (w : World) (d : Device) (pid : PeerId) (kid : KeypairId)
    (device : w.k.wg=some d) :
    (WG.indexReplaceHandshake pid kid).run w=.ok (sourceAnswer d pid,sourceFinal w d pid kid) := by
  have unchanged : {w.k with wg := some d}=w.k := by rw [←device]
  by_cases empty : ∀ x ∈ d.indexTable, (x.owner==.handshake pid)=false
  · have hashed : d.indexTable.any (·.owner==.handshake pid)=false :=
      List.any_eq_false.mpr (by simpa using empty)
    simp [WG.indexReplaceHandshake,indexHashed,WG.getDev,WG.modifyDev,getK,modifyK,branch,
      StateT.run_bind,StateT.run_pure,device,sourceAnswer,sourceFinal,hashed,unchanged]
    rw [ite_eq_left empty]
    rfl
  · have hashed : d.indexTable.any (·.owner==.handshake pid)=true := by
      cases h : d.indexTable.any (·.owner==.handshake pid)
      · exact False.elim (empty (by simpa using List.any_eq_false.mp h))
      · rfl
    simp [WG.indexReplaceHandshake,indexHashed,WG.getDev,WG.modifyDev,getK,modifyK,branch,
      StateT.run_bind,StateT.run_pure,device,sourceAnswer,sourceFinal,hashed,empty]
    rfl

theorem source_effect {w final : World} {d : Device} {pid : PeerId} {kid : KeypairId} {answer : Bool}
    (device : w.k.wg=some d)
    (accepted : (WG.indexReplaceHandshake pid kid).run w=.ok (answer,final)) :
    answer=sourceAnswer d pid ∧ final=sourceFinal w d pid kid := by
  rw [source_run w d pid kid device] at accepted
  exact ⟨(congrArg Prod.fst (Except.ok.inj accepted)).symm,
    (congrArg Prod.snd (Except.ok.inj accepted)).symm⟩

#print axioms source_run
end Binary.Pair.Replace
