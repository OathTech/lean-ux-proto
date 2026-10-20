import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTimerPointCanonical

/-! Zero-material expiry retains its original borrow and duplicate-work
choice. Its raw repayment is not replaced by the observed release callback. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points.Zero
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
open RetirementSecurity Queues.RxCredits

def beforeRepay (pid : PeerId) : WG.M Bool := do
  if ← branch .zeroKeyAlive !(← getPeer pid).isDead then
    peerGet pid
    if ← branch .zeroKeyAlreadyQueued ((← getDev).clearWorkQueue.contains pid
        && !(← peekQueuedUnit .clearPeerWorker pid)) then
      return true
    else
      recordQueued .clearPeerWorker pid
      modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]}
      return false
  return false

def afterRepay (pid : PeerId) (repay : Bool) : WG.M Unit :=
  if repay then peerPut (some pid) else pure ()

theorem factor (pid : PeerId) : expiredZeroKeyMaterial pid = beforeRepay pid >>= afterRepay pid := by
  unfold expiredZeroKeyMaterial beforeRepay
  simp only [bind_assoc]
  congr 1
  funext peer
  congr 1
  funext alive
  split
  · simp only [bind_assoc]
    congr 1
    funext ignored
    congr 1
    funext device
    congr 1
    funext selected
    congr 1
    funext pending
    split <;> simp only [pure_bind,afterRepay,ite_true,Bool.false_eq_true,ite_false,bind_assoc]
    simp only [bind_pure_unit]
  · rfl

theorem work_bind (body : WG.M α) (next : α → WG.M β) :
    WorkService.Points.wg (body >>= next) = (WorkService.Points.wg body >>= fun value => WorkService.Points.wg (next value)) :=
  Consume.Leaf.wg_bind body next

noncomputable def beforeShape (pid : PeerId) : WorkService.Points.Shape (wg (beforeRepay pid)) := by
  change WorkService.Points.Shape (WorkService.Points.wg (beforeRepay pid))
  unfold beforeRepay
  repeat' first
    | (work_wg_head peerGet; exact .native (.acquire _))
    | (work_wg_head modifyDev; refine .native (.change _ ?_); intro w;
        unfold StagedEntry.view Packets.epoch Staged.stagedAt PacketMaterial.view Packets.snapshot
          Packets.deviceStore TxDisposition.txPackets txQueueContents handoffTxView; cases w.dev <;> rfl)
    | (work_wg_head getPeer; exact .leaf (.native (.metadata _ (PeerMetadata.peerReadShape _))))
    | (work_wg_head getDev; exact .leaf (.native (.metadata _ PeerMetadata.deviceReadShape)))
    | (work_wg_head branch; exact .leaf (.native (.base (.basic (.branch _ _)))))
    | (work_wg_head peekQueuedUnit; exact .leaf (.native (.base (.ambient _))))
    | (work_wg_head recordQueued; exact .leaf (.native (.base (.ambient _))))
    | (work_wg_head Bind.bind; rw [work_bind]; apply WorkService.Points.Shape.bind)
    | (work_wg_head Pure.pure; exact .pure _)
    | maintenance_intro
    | split
    | (simp +failIfUnchanged only)

theorem product_factor (pid : PeerId) : wg (expiredZeroKeyMaterial pid) =
    (wg (beforeRepay pid) >>= fun repay => wg (afterRepay pid repay)) := by
  rw [factor]
  exact Consume.Leaf.wg_bind _ _

/-- The actual reached raw repayment entry follows the original borrowing
prefix and retains its packet account, including its exact current history. -/
theorem repayment_entry (before : Carrier h w)
    (leading : runPrefix (wg (beforeRepay pid)) w h = (.ok (true,u),middle)) : Carrier middle u :=
  (beforeShape pid).normal before leading
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Points.Zero
