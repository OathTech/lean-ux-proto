import Leanux.Proofs.WG.Queues.RxStableFrames
import Leanux.Proofs.WG.Queues.WorkReservations

/-! Preserve the actual typed TX/send delta at receive callback boundaries.
All temporary and durable reservations share the same reference bound. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes

/-- A source handoff exchanges only its supplied temporary reservations and
retains every newly acquired durable owner in the combined carrier budget. -/
theorem CarrierState.handoff (hi : CarrierState cs (loans ++ before) w)
    (step : Handoff w v before after delta) (keys : KeysCompatible v) :
    CarrierState cs (loans ++ after ++ delta.owners) v := by
  obtain ⟨inventory,queues,funded⟩ := step.funded hi.inventory hi.queues hi.funded
  exact ⟨inventory,queues,funded,keys⟩

theorem CarrierState.transfer_funded (hi : CarrierState cs loans w)
    (step : Transfer w v) (keys : KeysCompatible v) :
    ∃ delta, Handoff w v [] [] delta ∧ CarrierState cs (loans ++ delta.owners) v := by
  obtain ⟨delta,step⟩ := step
  obtain ⟨inventory,queues,_,funded⟩ := step.protect hi.inventory hi.queues hi.funded
  exact ⟨delta,step,inventory,queues,funded,keys⟩

/-- The actual consume callback preserves the supplied RX ledger and may
append TX batches and queued handshake work. No carrier phase is assumed. -/
theorem consume_state_funded {c : Carrier} (hi : CarrierState cs loans w)
    (hp : packetAt w c.packet = some pkt) (guard : pkt.peer = pid)
    (a b : Ambient)
    (run : ((consumeDataDone pid pkt ep).run w).run a = .ok ((out,v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧ CarrierState cs (loans ++ delta.owners) v := by
  have compatible : KeyCompatible pid pkt.keypair w := guard ▸ hi.packet_key hp
  exact hi.transfer_funded (consumeDataDone_handoff pid pkt ep compatible a b run)
    (consumeDataDone_keys pid pkt ep hi.keys compatible a b run)

theorem consume_stable_funded {c : Carrier} (hi : CarrierState cs loans w)
    (hs : StableRx stable w) (hp : packetAt w c.packet = some pkt)
    (guard : pkt.peer = pid) (a b : Ambient)
    (run : ((consumeDataDone pid pkt ep).run w).run a = .ok ((out,v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧ CarrierState cs (loans ++ delta.owners) v ∧
      StableRx stable v := by
  obtain ⟨delta,step,funded⟩ := consume_state_funded hi hp guard a b run
  exact ⟨delta,step,funded,stable_consumeDataDone pid pkt ep hs a b run⟩

/-- Concrete Stack replies return their source-attributed durable handoff;
normal error returns are included by the original execution contract. -/
theorem stack_state_funded (packets : List (List UInt8)) {w v : World}
    (hi : CarrierState cs loans w.wg)
    (run : (packets.forM Leanux.Env.deliverInner).run w = .ok ((),v)) :
    ∃ delta, Handoff w.wg v.wg [] [] delta ∧
      CarrierState cs (loans ++ delta.owners) v.wg := by
  obtain ⟨delta,step,inventory,queues,_,funded,keys⟩ :=
    stackForM_protection packets hi.inventory hi.queues hi.funded hi.keys run
  exact ⟨delta,step,inventory,queues,funded,keys⟩

theorem stack_stable_funded (packets : List (List UInt8)) {w v : World}
    (hi : CarrierState cs loans w.wg) (hs : StableRx stable w.wg)
    (run : (packets.forM Leanux.Env.deliverInner).run w = .ok ((),v)) :
    ∃ delta, Handoff w.wg v.wg [] [] delta ∧
      CarrierState cs (loans ++ delta.owners) v.wg ∧ StableRx stable v.wg := by
  obtain ⟨delta,step,funded⟩ := stack_state_funded packets hi run
  exact ⟨delta,step,funded,stable_stack packets hs hi.keys run⟩

end Leanux.Proofs.WG.Queues.RxCredits
