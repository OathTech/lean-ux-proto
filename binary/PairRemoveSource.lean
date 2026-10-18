import PairRemove

namespace Binary.Pair.Remove
open Leanux Leanux.WG

def sourceFinal (w : World) (d : Device) (owner : IndexOwner) : World :=
  {w with
    k := {w.k with wg := some {d with indexTable := d.indexTable.filter (fun e => !(e.owner==owner))}}
    steps := w.steps.push {decision := .idxRemoveHashed,outcome := d.indexTable.any (·.owner==owner),netRx := w.netRxSection}}

theorem source_run (w : World) (d : Device) (owner : IndexOwner) (device : w.k.wg=some d) :
    (WG.indexRemove owner).run w=.ok ((),sourceFinal w d owner) := by
  change ((do
    let dev ← WG.getDev
    let _ ← branch .idxRemoveHashed (dev.indexTable.any (·.owner==owner))
    WG.modifyDev fun dev => {dev with indexTable := dev.indexTable.filter (fun e => !(e.owner==owner))}) : M Unit).run w=_
  simp [WG.getDev,WG.modifyDev,getK,modifyK,branch,sourceFinal,
    StateT.run_bind,StateT.run_pure,device]
  rfl

theorem source_effect {w final : World} {d : Device} {owner : IndexOwner}
    (device : w.k.wg=some d) (accepted : (WG.indexRemove owner).run w=.ok ((),final)) :
    final=sourceFinal w d owner := by
  rw [source_run w d owner device] at accepted
  exact (congrArg Prod.snd (Except.ok.inj accepted)).symm

#print axioms source_run
#print axioms source_effect
end Binary.Pair.Remove
