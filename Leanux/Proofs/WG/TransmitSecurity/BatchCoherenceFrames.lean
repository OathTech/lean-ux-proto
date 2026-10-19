import Leanux.Proofs.WG.TransmitSecurity.BatchCoherence
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceKeyFrames

/-! Frames for peer/key homogeneity of queued TX batches. Queue removal and
packet disposal are allowed; replacement by unrelated material is not. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits
variable {w v : WGWorld}

def view (w : WGWorld) := (handoffTxView w,PacketMaterial.view w)

theorem Inv.frame (before : Inv w) (same : view v = view w) : Inv v := by
  obtain ⟨queues,packets⟩ := Prod.mk.inj same
  intro pid p found items member
  have point : handoffTxView v pid = some p.txQueue.all := by
    simpa [handoffTxView,peerAt] using congrArg (Option.map (fun p => p.txQueue.all)) found
  rw [queues] at point
  obtain ⟨old,resident,queue⟩ := Option.map_eq_some_iff.mp point
  obtain ⟨slot,aligned⟩ := before pid old resident items (queue.symm ▸ member)
  exact ⟨slot,aligned.frame packets⟩

theorem frame {action : WG.M α} (same : SameView view action) : Preserves Inv action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact before.frame ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)

theorem pair {action : WG.M α} (queues : SameView handoffTxView action)
    (packets : SameView PacketMaterial.view action) : SameView view action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  exact Prod.ext ((ProjectedAction.iff_run_ambient _ _ _).mp queues w a result v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp packets w a result v b run)

theorem aligned {action : WG.M α} (same : SameView PacketMaterial.view action) :
    Preserves (fun w => Aligned w pid slot items) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact before.frame ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)

theorem product_aligned {action : Leanux.M α}
    (same : SameView (fun w : World => PacketMaterial.view w.wg) action) :
    Preserves (fun w : World => Aligned w.wg pid slot items) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  exact before.frame ((ProjectedAction.iff_run _ _ _).mp same w result v run)

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence
