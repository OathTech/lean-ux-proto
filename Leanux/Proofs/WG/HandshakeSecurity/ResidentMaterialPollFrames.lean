import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialCarrierCallbacks
import Leanux.Proofs.WG.RetirementSecurity.RxPollOccurrenceFrames

/-! Native poll leaves preserve resident TX key material. RX packet disposal
and replay-window writes cannot replace a TX reference's allocation core. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder RetirementSecurity

theorem lower_slot_fields {action : WG.M α} (same : SameView CurrentSlots.fields action) :
    Preserves (Lower bound) action := lower_frame (same.factor Prod.fst)

theorem counter (kid : KeypairId) (nonce : Nat) : Preserves (Inv h) (counterValidate kid nonce) :=
  frame (PacketOrigins.snapshot_wire (RxPollOccurrences.counter_wire kid nonce))
    (core_of_same (counter_core kid nonce))
    (fun _ => lower_slot_fields
      ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotPoll.«0».Leanux.Proofs.WG.CurrentSlots.counter_fields) kid nonce))

theorem read_rx (id : SkbId) : Preserves (Inv h) (getRxSkb id) :=
  frame (PacketOrigins.snapshot_wire (ReceiveOccurrences.get_rx_wire id))
    (core_of_same ((skb_allocation_view (SkbStore.getRx id)).factor Prod.fst))
    (fun _ => lower_frame ((skb_allocation_view (SkbStore.getRx id)).factor (fun fields => fields.2.1)))

theorem free_rx (id : SkbId) : Preserves (Inv h) (freeRxSkb id) :=
  frame (PacketOrigins.snapshot_wire (ReceiveOccurrences.free_rx_wire id))
    (core_of_same ((skb_allocation_view (SkbStore.freeRx id)).factor Prod.fst))
    (fun _ => lower_frame ((skb_allocation_view (SkbStore.freeRx id)).factor (fun fields => fields.2.1)))

theorem drop_rx (pid : PeerId) : Preserves (Inv h) (dropRxQueue pid) := by
  unfold dropRxQueue
  repeat' resident_staging_step

macro "resident_poll_frame" : tactic => `(tactic| first
  | (rx_retention_head PrevQueue.peek; exact store (prevQueuePeek_sameWGStore _))
  | (rx_retention_head endpointFromSkb; exact store (endpointFromSkb_sameWGStore _))
  | (rx_retention_head getRxSkb; exact read_rx _)
  | (rx_retention_head freeRxSkb; exact free_rx _)
  | (rx_retention_head dropRxQueue; exact drop_rx _)
  | (rx_retention_head counterValidate; exact counter _ _)
  | (rx_retention_head unsupported; exact hoare_liftAmbient (AmbientM.unsupported _) _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi run
     cases run)
  | resident_staging_step)

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
