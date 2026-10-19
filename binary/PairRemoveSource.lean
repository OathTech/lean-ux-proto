import SourceAdapter
import PairRemove

namespace Binary.Pair.Remove
open Leanux Leanux.WG

def sourceFinal (w : World) (d : Device) (owner : IndexOwner) : World :=
  {w with wg := {w.wg with dev := some {d with indexTable := d.indexTable.filter (fun e => !(e.owner==owner))}}, ambient := {w.ambient with steps := w.steps.push {decision := .idxRemoveHashed,outcome := d.indexTable.any (·.owner==owner),netRx := w.netRxSection}}}

theorem source_run (w : World) (d : Device) (owner : IndexOwner) (device : w.wg.dev=some d) :
    (Source.indexRemove owner).run w=.ok ((),sourceFinal w d owner) := by
  change (liftWG (liftIndex (do
    _ ← branch .idxRemoveHashed ((← get).any (·.owner==owner))
    modify fun entries => entries.filter (fun e => !(e.owner==owner))))).run w=_
  simp [Except.pure, Except.bind, StateT.run, bind, StateT.bind, StateT.lift, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftM, monadLift, MonadLift.monadLift, liftWG, liftAmbient, AmbientM.branch, WG.getDev, WG.modifyDev, liftIndex, branch, sourceFinal, device]


theorem source_effect {w final : World} {d : Device} {owner : IndexOwner}
    (device : w.wg.dev=some d) (accepted : (Source.indexRemove owner).run w=.ok ((),final)) :
    final=sourceFinal w d owner := by
  rw [source_run w d owner device] at accepted
  exact (congrArg Prod.snd (Except.ok.inj accepted)).symm

#print axioms source_run
#print axioms source_effect
end Binary.Pair.Remove
