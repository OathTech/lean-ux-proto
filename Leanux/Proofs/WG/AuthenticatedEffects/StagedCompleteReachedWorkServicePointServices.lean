import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkServicePointQueued

/-! Original scheduled and flushed services retain selection, dequeue, native
section records, maintenance and repayment in their actual order. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal RetirementSecurity

theorem lift_bind (body : Leanux.M α) (next : α → Leanux.M β) :
    (liftPrefix (body >>= next) : PrefixM Event β) = (liftPrefix body >>= fun value => liftPrefix (next value)) := by
  funext w h
  change runPrefix (liftPrefix (body >>= next)) w h = runPrefix (liftPrefix body >>= fun value => liftPrefix (next value)) w h
  rw [runPrefix_bind,runPrefix_lift,runPrefix_lift]
  simp only [StateT.run_bind]
  cases body.run w <;> rfl

noncomputable def nativeBindShape (body : Leanux.M α) (next : α → Leanux.M β)
    (head : Shape (liftPrefix body)) (tail : ∀ value, Shape (liftPrefix (next value))) :
    Shape (liftPrefix (body >>= next)) := by
  rw [lift_bind]
  exact .bind head tail

noncomputable def clearShape (pid : PeerId) :
    Shape (liftWGObserver (NestedPeerRelease.clearWith (Driver.nestedOps hooks) pid)) := by
  apply Shape.marked (.clear pid)
  unfold NestedPeerRelease.clearWith
  exact stateBindShape _ _ (.leaf (handshakeClearLeaf pid)) fun _ =>
    stateBindShape _ _ (.leaf (keysClearLeaf pid)) fun _ => .child (.release (some pid))

noncomputable def clearEraseShape (pid : PeerId) :
    Shape (wg (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})) := by
  refine .native (.change _ ?_)
  intro w
  unfold StagedEntry.view Packets.epoch Staged.stagedAt PacketMaterial.view
    Packets.snapshot Packets.deviceStore TxDisposition.txPackets txQueueContents Queues.RxCredits.handoffTxView
  cases w.dev <;> rfl

noncomputable def clearEraseNativeShape (pid : PeerId) :
    Shape (liftPrefix (liftWG (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}))) := by
  simpa only [wg,Consume.Leaf.wg,Consume.Points.wg,liftWGObserver_lift] using clearEraseShape pid

noncomputable def flushedClearShape (pid : PeerId) :
    Shape (liftWGObserver (NestedPeerRelease.flushedClearWith (Driver.nestedOps hooks) pid)) := by
  apply Shape.marked (.flushedClear pid)
  unfold NestedPeerRelease.flushedClearWith
  exact stateBindShape _ _ (clearEraseShape pid) fun _ =>
    stateBindShape _ _ (.leaf (.native (.base (.ambient (AmbientM.hidden (.sectionStart .clearPeerWorker)))))) fun _ =>
      stateBindShape _ _ (clearShape pid) fun _ =>
        stateBindShape _ _ (.leaf (.native (.base (.ambient (AmbientM.hidden (.sectionStop .clearPeerWorker)))))) fun _ =>
          .pure ()

noncomputable def selectSendShape : Shape (liftPrefix SendWorkCauses.select) := by
  unfold SendWorkCauses.select
  apply nativeBindShape _ _
    (by rw [← liftWGObserver_lift]; exact .leaf (.native (.base .device)))
  intro device
  split
  · apply nativeBindShape _ _ (.native (.ambient (AmbientM.peekUnit .sendWorker)))
    intro selected
    cases selected with
    | none => exact .pure _
    | some unit => exact .native (.ambient (AmbientM.resolveUnit .sendWorker unit device.sendWorkQueue))
  · exact .leaf (.native (.base (.basic (.invariant _))))

noncomputable def scheduledSendShape : Shape (Driver.sendWorkerObserved hooks) := by
  apply Shape.marked .scheduledSend
  unfold Driver.sendWorkerObserved HandshakeSecurity.SendExchange.oneWith
  exact .bind selectSendShape (fun pid => .child (.flushedSend pid))

noncomputable def clearSectionShape (pid : PeerId) :
    Shape (runWorkerPrefix .clearPeerWorker (liftWGObserver (NestedPeerRelease.clearWith (Driver.nestedOps hooks) pid))) := by
  unfold runWorkerPrefix
  simp only [reduceBEq,bind_pure_comp]
  exact .bind (.native (.ambient (AmbientM.hidden (.sectionStart .clearPeerWorker)))) fun _ =>
    .bind (clearShape pid) fun _ =>
      .bind (.native (.ambient (AmbientM.hidden (.sectionStop .clearPeerWorker)))) fun _ => .pure ()

noncomputable def scheduledClearShape : Shape (Driver.clearWorkerObserved hooks) := by
  apply Shape.marked .scheduledClear
  unfold Driver.clearWorkerObserved NestedPeerRelease.oneClearWith
  apply Shape.bind (body := liftPrefix (liftWG getDev))
    (by rw [← liftWGObserver_lift]; exact .leaf (.native (.base .device)))
  intro device
  split
  · apply Shape.bind (.native (.ambient (AmbientM.peekUnit .clearPeerWorker)))
    intro selected
    cases selected with
    | none =>
      apply Shape.bind (.pure _)
      intro pid
      exact .bind (clearEraseNativeShape pid) (fun _ => clearSectionShape pid)
    | some unit =>
      apply Shape.bind (.native (.ambient (AmbientM.resolveUnit .clearPeerWorker unit device.clearWorkQueue)))
      intro pid
      exact .bind (clearEraseNativeShape pid) (fun _ => clearSectionShape pid)
  · exact .leaf (.native (.base (.basic (.invariant _))))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
