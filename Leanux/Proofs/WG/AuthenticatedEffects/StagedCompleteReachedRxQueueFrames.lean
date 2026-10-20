import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRxQueueSource

/-! The saved peer read justifies its later queue update; every receive-admission cut preserves the existing complete TX account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RxQueueAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem install_frame (skb : SkbId) : SameView StagedEntry.view (install skb) := by
  intro initial
  change Preserves (fun w=>StagedEntry.view w=initial) _
  unfold install front
  simp only [bind_assoc]
  apply preserves_bind (CompleteDecrypt.set_rx _ _ initial)
  intro ignored
  apply preserves_bind (CompletePollNative.get_rx _ initial)
  intro packet
  apply hoare_bind _ _ (SavedFrames.read packet.peer (·=initial))
  intro peer
  unfold branch
  apply hoare_bind _ _ (hoare_liftAmbient _ _)
  intro full
  cases full with
  | true=>
      simp only [ite_true,pure_bind,installFinish]
      exact hoare_consequence (preserves_pure false) (fun _ before=>before.1) (fun _ _ before=>before)
  | false=>
      simp only [Bool.false_eq_true,ite_false,pure_bind,installFinish]
      apply hoare_bind _ _ (SavedFrames.write_saved packet.peer peer {peer with rxQueue:=peer.rxQueue.enqueue skb}
        (·=initial) ⟨rfl,rfl,rfl⟩)
      intro ignored
      exact hoare_consequence (preserves_pure true) (fun _ before=>before.1) (fun _ _ before=>before)

theorem Point.frame (point : Point skb w a v b) : StagedEntry.view v=StagedEntry.view w := by
  cases point with
  | front point=>exact point.frame
  | written prepared written=>
      exact (ProjectedAction.iff_run_ambient _ _ _).mp (install_frame skb) _ _ _ _ _
        (written_install prepared written)
  | afterInstall installed point=>exact point.frame.trans ((ProjectedAction.iff_run_ambient _ _ _).mp (install_frame skb) _ _ _ _ _ installed)
  | returned performed=>exact (ProjectedAction.iff_run_ambient _ _ _).mp (CompleteIngress.enqueue skb) _ _ _ _ _ performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RxQueueAccess
