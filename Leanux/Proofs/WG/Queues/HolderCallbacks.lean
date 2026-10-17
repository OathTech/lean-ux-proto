import Leanux.Proofs.WG.Queues.PassiveHolders

/-! Concrete receive callbacks retain the entire aligned durable account,
including their freshly acquired TX/send references. This is a normal source
cut, not initialized runner closure. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes

/-- Keep the supplied carriers, independent stable ledger and every durable
holder through the actual receive completion, with its exact acquired delta. -/
theorem consume_normal {holders : DurableHolders} {c : Carrier}
    (hi : holders.Funded cs loans w) (hs : StableRx stable w)
    (stored : packetAt w c.packet = some pkt) (guard : pkt.peer = pid)
    (a b : Ambient)
    (run : ((consumeDataDone pid pkt ep).run w).run a = .ok ((result,v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧
      (holders.absorb delta).Funded cs loans v ∧ StableRx stable v := by
  have compatible : KeyCompatible pid pkt.keypair w := guard ▸ hi.carriers.packet_key stored
  have transfer := consumeDataDone_handoff pid pkt ep compatible a b run
  have keys := consumeDataDone_keys pid pkt ep hi.carriers.keys compatible a b run
  have passive := (hoare_iff_run_ambient _ _ _).mp
    (PassiveHolders.consumeDataDone_preserves pid pkt ep (passiveView w))
    w a result v b rfl run
  obtain ⟨delta,handoff,funded⟩ := hi.transfer transfer keys passive
  exact ⟨delta,handoff,funded,stable_consumeDataDone pid pkt ep hs a b run⟩

/-- The native product Stack callback both preserves old obligations and
retains new TX/send holders aligned with its actual final queues. -/
theorem stack_normal {holders : DurableHolders} {w v : World}
    (packets : List (List UInt8)) (hi : holders.Funded cs loans w.wg)
    (hs : StableRx stable w.wg)
    (run : (packets.forM Leanux.Env.deliverInner).run w = .ok ((),v)) :
    ∃ delta, Handoff w.wg v.wg [] [] delta ∧
      (holders.absorb delta).Funded cs loans v.wg ∧ StableRx stable v.wg := by
  have post := (hoare_iff_run _ _ _).mp (stackForM_stack w.wg packets)
    w () v ⟨Transfer.refl w.wg,hi.carriers.keys⟩ run
  have passive := (hoare_iff_run _ _ _).mp
    (PassiveHolders.stack_preserves packets (passiveView w.wg)) w () v rfl run
  obtain ⟨delta,handoff,funded⟩ := hi.transfer post.1 post.2 passive
  exact ⟨delta,handoff,funded,stable_stack packets hs hi.carriers.keys run⟩

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
