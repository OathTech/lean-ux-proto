import Leanux.Proofs.WG.Index.PollCoreObservationSource
import Leanux.Proofs.WG.Index.PollCoreCompositionSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.PollCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem poll_observed (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun _ w=>TimerCore.Ready w.wg) (fun _=>True) (RxJoint.poll pid budget) := by
  rw [RxJoint.PollSource.poll_factor]
  apply PollSource.poll_preserves_fixed_variant (fun _ w=>Loop pid w.wg)
    (fun _ w=>TimerCore.Ready w.wg) (fun _=>True) (fun {_} a=>a) _ _ pid budget
    (fun _ _ _=>True.intro) (fun _ _ _=>True.intro) (fun _ _ pre=>Or.inl pre)
  · exact native_observed _ _ _ (RxJoint.peekAccess_erases pid)
      (native_loop pid _ (peek_view_index_variant pid) (fun entry=>DriverTags.Poll.peek_retained entry pid))
  · intro first
    exact native_observed _ _ _ (RxJoint.readyAccess_erases first)
      (native_loop pid _ (ready_ready first) (fun entry=>DriverTags.Poll.ready_retained entry first))
  · exact capture _
  · intro n skb stamp
    unfold RxJoint.drop
    exact (native_observed _ _ _ (rxDropPeekedPrefix_erases pid)
      (native_loop pid _ (drop_ready pid) (fun entry=>DriverTags.Poll.drop_retained entry pid))).bind
        (fun _=>emitted _ _)
  · intro n skb stamp pkt
    exact receipt _ _ _ (ambient _ (AmbientM.branch .rxPollNotCrypted (pkt.state != .crypted)))
  · intro n skb stamp pkt
    exact receipt _ _ _ (native_observed _ _ _ (counterValidatePrefix_erases pkt.keypair pkt.nonce)
      (native_loop pid _ (counter_ready pkt.keypair pkt.nonce)
        (fun entry=>DriverTags.Poll.counter_retained entry pkt.keypair pkt.nonce)))
  · intro n skb stamp pkt
    exact receipt _ _ _ (lifted _ _ (PublicationPoll.native_product _ _
      (native_loop pid _ (store_ready (endpointFromSkb_sameWGStore pkt.source))
        (fun entry=>DriverTags.Silent.of_frame entry _ (DriverTags.store_frame (endpointFromSkb_sameWGStore pkt.source))))))
  · exact consume_loop pid
  · intro kid
    exact native_observed _ _ _ (keypairPutPrefix_erases (some kid) false)
      (native_loop pid _ (keypair_ready (some kid) false)
        (fun entry=>DriverTags.Silent.keypairPut entry (some kid) false))
  · exact native_observed _ _ _ (peerPutMixed_erases (some pid)) (peer_loop pid)
  · intro skb
    exact native_observed _ _ _ (freeRxSkbPrefix_erases skb)
      (native_loop pid _ (packet_ready (SkbStore.freeRx skb))
        (fun entry=>DriverTags.Silent.of_frame entry _ (DriverTags.Silent.packet_frame (SkbStore.freeRx skb))))
  · exact complete_observed pid
  · intro b; exact ambient _ (AmbientM.branch .rxPollNoBudget b)
  · intro b; exact ambient _ (AmbientM.branch .rxPollCounterInvalid b)
  · intro b; exact ambient _ (AmbientM.branch .rxPollEndpointFailed b)
  · intro b; exact ambient _ (AmbientM.branch .rxPollFree b)
  · intro b; exact ambient _ (AmbientM.branch .rxPollBudgetDone b)
  · intro b; exact ambient _ (AmbientM.branch .rxPollComplete b)
  · exact gro_receive _ (stack_loop pid)
  · exact gro_flush _ TransmitCore.stack_ready

theorem poll_ready (pid : PeerId) (budget : Nat) :
    Preserves (fun w : World=>TimerCore.Ready w.wg)
      (rxPoll pid budget (fun packets=>packets.forM Env.deliverInner)) :=
  original _ _ _ (RxJoint.poll_erases pid budget) (poll_observed pid budget)

end Leanux.Proofs.WG.Index.PollCore
