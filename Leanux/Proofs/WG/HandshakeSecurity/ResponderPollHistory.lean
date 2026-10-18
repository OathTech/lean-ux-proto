import Leanux.Proofs.WG.HandshakeSecurity.ResponderGroHistory

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.History
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues RxJoint Origins Origins.Retaining

theorem ready_rule (first : Option SkbId) (base : List Nat) :
    PrefixPreserves (State base) (Checks base) (access (liftWGObserver (readyAccess first))) := by
  apply native_access _ _ base (readyAccess_erases first)
  intro confirmed
  unfold WG.andM branch invariant
  repeat' first
    | (rx_retention_head getRxSkb; exact read_native _ confirmed)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem endpoint_rule (n id : Nat) (stamp : PacketStamp) (pkt : RxPacket)
    (base : List Nat) :
    PrefixPreserves (State base) (Checks base)
      (receiptObserved (liftPrefix (liftWG (endpointFromSkb pkt.source)))
        (Event.checkedEndpoint n id stamp pkt)) :=
  receipt_rule _ _ base
    (lift_rule _ base (fun confirmed => PublicationPoll.native_product _ _
      (native_store (endpointFromSkb_sameWGStore _) confirmed))) (fun _ => rfl)

theorem keep_bind (g : Obs α) (f : α → Obs β) (base : List Nat)
    (hg : PrefixPreserves (State base) (Checks base) g)
    (hf : ∀ x, PrefixPreserves (State base) (Checks base) (f x)) :
    PrefixPreserves (State base) (Checks base) (g >>= f) := hg.bind hf

macro "responder_poll_step " base:term " with " H1:term ", " slots:term ", " stack:term : tactic => `(tactic| first
  | rx_phase_reduce
  | (rx_phase_head plain Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => hi.2) _)
  | (rx_phase_head plain capture; apply keep_bind _ _ $base (capture_rule _ $base))
  | (rx_phase_head plain drop; apply keep_bind _ _ $base (drop_rule _ _ _ _ $base))
  | (rx_phase_head plain RxJoint.consume; apply keep_bind _ _ $base (History.consume $H1 $slots $base _ _ _ _ _ _))
  | (rx_phase_head plain receive; apply keep_bind _ _ $base (receive_rule _ _ $base $stack))
  | (rx_phase_head plain flushAll; apply keep_bind _ _ $base (flushAll_rule _ $base $stack))
  | (rx_phase_head plain peekAccess; apply keep_bind _ _ $base (native_access _ _ $base
      (peekAccess_erases _) (peek_native _)))
  | (rx_phase_head plain readyAccess; apply keep_bind _ _ $base (ready_rule _ $base))
  | (rx_phase_head plain completeAccess; apply keep_bind _ _ $base (native_access _ _ $base
      (completeAccess_erases _) (complete_native _)))
  | (rx_phase_head receipt branch; apply keep_bind _ _ $base (receipt_rule _ _ $base
      (lift_rule _ $base (fun _ => productAmbient_spec (AmbientM.branch _ _) _ (fun _ _ hi => hi))) (fun _ => rfl)))
  | (rx_phase_head receipt counterValidatePrefix; apply keep_bind _ _ $base (receipt_rule _ _ $base
      (native_access _ _ $base (counterValidatePrefix_erases _ _) (counter_native _ _)) (fun _ => rfl)))
  | (rx_phase_head receipt endpointFromSkb; apply keep_bind _ _ $base (endpoint_rule _ _ _ _ $base))
  | (rx_phase_head plain keypairPutPrefix; apply keep_bind _ _ $base (native_access _ _ $base
      (keypairPutPrefix_erases _ _) (keypairPut_native _ _)))
  | (rx_phase_head plain peerPutMixed; apply keep_bind _ _ $base (native_access _ _ $base
      (peerPutMixed_erases _) (peerPut_native _)))
  | (rx_phase_head plain freeRxSkbPrefix; apply keep_bind _ _ $base (native_access _ _ $base
      (freeRxSkbPrefix_erases _) (free_native _)))
  | (rx_phase_head plain branch; apply keep_bind _ _ $base (lift_rule _ $base
      (fun _ => productAmbient_spec (AmbientM.branch _ _) _ (fun _ _ hi => hi))))
  | (rx_phase_head plain invariant; apply keep_bind _ _ $base (lift_rule _ $base
      (fun _ => productAmbient_spec (AmbientM.invariant _) _ (fun _ _ hi => hi))))
  | (rx_phase_head plain unsupported; apply keep_bind _ _ $base (lift_rule _ $base
      (fun _ => productAmbient_spec (AmbientM.unsupported _) _ (fun _ _ hi => hi))))
  | (rx_phase_head plain ite; apply PrefixPreserves.ite)
  | rx_phase_intro
  | rx_phase_match)

/-- The actual poll carries the current responder authorization through every
native receive operation. The concrete stack callback's normal-state contract
remains visible here; late Stop retains all checked consume entries. -/
theorem poll (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges)
    (stack : ∀ bytes confirmed, Preserves (fun w : World => Native confirmed w.wg)
      (Leanux.Env.deliverInner bytes)) (pid : PeerId) (budget : Nat) (base : List Nat) :
    PrefixPreserves (State base) (Checks base) (RxJoint.poll pid budget) := by
  unfold RxJoint.poll
  repeat' first
    | exact fun _ _ hi => hi.2
    | responder_poll_step base with H1, slots, stack
    | (rx_phase_head plain ForIn.forIn
       apply keep_bind _ _ base
       first | apply PrefixPreserves.range | apply PrefixPreserves.forIn)
    | exact And.right ‹State base _ _›

end Leanux.Proofs.WG.HandshakeSecurity.Responder.History
