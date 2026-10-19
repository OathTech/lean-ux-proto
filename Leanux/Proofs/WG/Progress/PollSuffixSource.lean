import Leanux.Proofs.WG.Progress.RecordObservationSource
import Leanux.Proofs.WG.Progress.PollSuffixFrames
import Leanux.Proofs.WG.Progress.ConsumeSuffixSource
import Leanux.Proofs.WG.Progress.EncryptSuffixFrames
import Leanux.Proofs.WG.Queues.PollPreservation

/-! The existing stamped poll and GRO factories retain record suffixes. The only separate source obligation is the exact original Stack delivery callback; no successful callback or poll return is assumed. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues

theorem poll_consume_retains (records : List HiddenRecord) (pid occurrence id : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (ep : Endpoint) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True)
      (RxJoint.consume pid occurrence id stamp pkt ep) := by
  unfold RxJoint.consume
  apply PrefixPreserves.bind
  · exact (joint_native_retains records _ _ (consumeDataDonePrefix_erases pid pkt ep)
      (consumeDataDone_retains records pid pkt ep)).captureObserved
  · intro r
    apply (suffix_emitted records _).bind
    intro _
    split
    · exact PrefixPreserves.pure (fun _ _ _=>True.intro) _
    · exact (suffix_emitted records _).bind
        (fun _=>PrefixPreserves.pure (fun _ _ _=>True.intro) _)

theorem gro_receive_retains (records : List HiddenRecord)
    (stack : ∀ bytes,Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.deliverInner bytes))
    (g : RxJoint.Gro) (e : RxJoint.Entry) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) (RxJoint.receive g e) := by
  rw [RxJoint.GroSource.receive_factor]
  apply RxJoint.GroSource.receive_preserves id _ (fun _ _ _=>True.intro)
  · intro e h w hi; exact hi
  · intro bytes
    exact product_observed records _ _ (RxJoint.access_appends _)
      (RxJoint.access_erases (stackReceivePrefix_erases bytes)) (stack bytes)
  · intro e w h x v t _ _ hi; exact hi

theorem gro_flush_retains (records : List HiddenRecord)
    (stack : ∀ bytes,Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.deliverInner bytes))
    (g : RxJoint.Gro) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) (RxJoint.flushAll g) := by
  rw [RxJoint.GroSource.flushAll_factor]
  apply RxJoint.GroSource.flushAll_preserves id _ (fun _ _ _=>True.intro)
  · intro e h w hi; exact hi
  · intro bytes
    exact product_observed records _ _ (RxJoint.access_appends _)
      (RxJoint.access_erases (stackReceivePrefix_erases bytes)) (stack bytes)
  · intro e w h x v t _ _ hi; exact hi

theorem poll_retains_of_stack (records : List HiddenRecord)
    (stack : ∀ bytes,Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.deliverInner bytes))
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun _ (w : World)=>Tail records w.ambient.hidden) (fun _=>True) (RxJoint.poll pid budget) := by
  rw [RxJoint.PollSource.poll_factor]
  apply RxJoint.PollSource.poll_preserves (fun {_} a=>a) _ _ (fun _ _ _=>True.intro)
  · intro peer; exact joint_native_retains records _ _ (RxJoint.peekAccess_erases peer) (rx_peek_retains records peer)
  · intro first; exact joint_native_retains records _ _ (RxJoint.readyAccess_erases first) (rx_ready_retains records first)
  · exact poll_capture_retains records
  · intro peer n skb stamp
    unfold RxJoint.drop
    exact (joint_native_retains records _ _ (rxDropPeekedPrefix_erases peer) (rx_drop_retains records peer)).bind
      (fun _=>suffix_emitted records _)
  · intro n skb stamp pkt
    exact suffix_receipt records _ _
      (product_lift_retains records _ (product_branch_retains records _ _))
  · intro n skb stamp pkt
    exact suffix_receipt records _ _ (joint_native_retains records _ _
      (counterValidatePrefix_erases pkt.keypair pkt.nonce) (counterValidate_retains records pkt.keypair pkt.nonce))
  · intro n skb stamp pkt
    exact suffix_receipt records _ _ (product_lift_retains records _
      (native_product records _ (endpointFromSkb_retains records pkt.source)))
  · exact poll_consume_retains records
  · intro kid; exact joint_native_retains records _ _ (keypairPutPrefix_erases (some kid) false)
      (keypairPut_retains records (some kid) false)
  · intro peer; exact joint_native_retains records _ _ (peerPutMixed_erases (some peer))
      (peerPut_retains records (some peer))
  · intro skb; exact joint_native_retains records _ _ (freeRxSkbPrefix_erases skb) (freeRx_retains records skb)
  · intro peer; exact joint_native_retains records _ _ (RxJoint.completeAccess_erases peer) (rx_complete_retains records peer)
  · intro b; exact product_lift_retains records _ (product_branch_retains records _ _)
  · intro b; exact product_lift_retains records _ (product_branch_retains records _ _)
  · intro b; exact product_lift_retains records _ (product_branch_retains records _ _)
  · intro b; exact product_lift_retains records _ (product_branch_retains records _ _)
  · intro b; exact product_lift_retains records _ (product_branch_retains records _ _)
  · intro b; exact product_lift_retains records _ (product_branch_retains records _ _)
  · exact gro_receive_retains records stack
  · exact gro_flush_retains records stack

theorem rxPoll_retains_of_stack (records : List HiddenRecord)
    (stack : ∀ bytes,Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.deliverInner bytes))
    (pid : PeerId) (budget : Nat) :
    Preserves (fun w : World=>Tail records w.ambient.hidden)
      (rxPoll pid budget (fun pkts=>pkts.forM Env.deliverInner)) :=
  observed_product records _ _ (RxJoint.poll_erases pid budget) (poll_retains_of_stack records stack pid budget)
end Leanux.Proofs.WG.Progress.RecordSuffix
