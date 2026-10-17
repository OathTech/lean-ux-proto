import Leanux.Proofs.WG.Queues.HolderWorkFrames
import Leanux.Proofs.WG.Queues.HolderPollCallbacks
import Leanux.Proofs.WG.Queues.RxPollBoundary

/-! The ordinary poll source steps retain durable holder fields. RX queue and
packet changes remain covered by their existing phase contracts. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open RxJoint PollCarrier

theorem peek_frame (pid : PeerId) (initial) : Preserves (Frame initial) (peekRxQueue pid) := by
  unfold peekRxQueue
  repeat' first
    | (rx_retention_head PrevQueue.peek; unfold PrevQueue.peek)
    | (rx_retention_head PrevQueue.dequeue; unfold PrevQueue.dequeue)
    | (rx_retention_head invariant; unfold invariant)
    | (rx_retention_head unsupported; unfold unsupported)
    | (rx_retention_head branch; unfold branch)
    | holder_work_step initial

theorem drop_frame (pid : PeerId) (initial) : Preserves (Frame initial) (dropRxQueue pid) := by
  unfold dropRxQueue
  repeat' holder_work_step initial

theorem complete_frame (pid : PeerId) (initial) : Preserves (Frame initial) (completeRxQueue pid) := by
  unfold completeRxQueue
  repeat' holder_work_step initial

theorem counter_frame (kid : KeypairId) (nonce : Nat) (initial) :
    Preserves (Frame initial) (counterValidate kid nonce) := by
  unfold counterValidate WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,
    Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Frame initial)
       intro x b
       change Preserves (Frame initial) _)
    | holder_work_step initial

theorem cleanup_frame (skb : SkbId) (pkt : RxPacket) (flag : Bool) (initial) :
    Preserves (Frame initial) (cleanup skb pkt flag) := by
  unfold cleanup
  repeat' first
    | rxstack_preserves_join
    | (rx_retention_head branch; unfold branch)
    | (rx_retention_head peerPut; exact HolderWorkFrames.peerPut_frame _ initial)
    | (rx_retention_head keypairPut
       exact HolderWorkFrames.keypairPut_frame _ _ initial)
    | (rx_retention_head freeRxSkb; unfold freeRxSkb)
    | (rx_retention_head liftSkb
       apply hoare_liftSkb
       intro w d store hi hd
       exact hi.trans (by constructor <;> first | (simp [passiveView,sendView,hd]) |
         (intro q xs h; simpa [handoffTxView,hd] using h)))
    | holder_work_step initial

/-- Observer-normal lifting also covers captures whose output carries an entry
stamp. It uses their actual endpoint and preserves their original journal. -/
theorem accounted_observer {α : Type}
    {P : Reservations → List RxJoint.Event → World → Prop}
    {Q : Reservations → α → List RxJoint.Event → World → Prop}
    (action : RxJoint.Obs α) (appends : Appends action)
    (old : ∀ loans, PrefixEnsures (P loans) (fun _ => True) action (Q loans))
    (frame : ∀ w h x v, (runPrefix action w h).1 = .ok (x,v) → Frame w.wg v.wg)
    (loans : Reservations) :
    PrefixEnsures (Accounted P loans) (fun _ => True) action
      (fun x => Accounted (fun owners => Q owners x) loans) := by
  apply normal_spec appends
  intro w h x v hi run
  obtain ⟨holders,aligned,phase⟩ := hi
  have post := (old (holders.owners ++ loans) w h phase).choose_spec.2.2
  rw [run] at post
  exact ⟨holders,aligned.frame (frame w h x v run),post⟩

theorem native_frame (a : WG.M α) (ha : ∀ initial, Preserves (Frame initial) a)
    (w v : World) (x : α) (run : (liftWG a).run w = .ok (x,v)) : Frame w.wg v.wg :=
  (hoare_iff_run_ambient _ _ _).mp (ha w.wg) w.wg w.ambient x v.wg v.ambient
    (Frame.refl w.wg)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) _ w v x run)

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
