import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCleanupPrimitiveSource

/-! Exact native getter/erase states and the missing-cell projection. These
facts do not claim that the old pending ledger backs the erased cell. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CleanupPrimitive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation HandshakeSecurity.StagedConservation
open CompleteCarrier StagedTerminalComplete

theorem read_accounted (skb : SkbId)
    (before : Accounted history ledger debts locals w) :
    Accounted (history ++ [readEvent w skb]) ledger debts locals w := by
  refine ⟨before.entry.views _ ?_ rfl rfl rfl rfl rfl rfl,before.complete.append_quiet ?_⟩
  · intro event member
    cases List.mem_singleton.mp member
    rfl
  · intro event member
    cases List.mem_singleton.mp member
    intro position
    rfl

theorem native_parts (skb : SkbId) (w v : World)
    (native : (liftWG (freeTxSkb skb)).run w = .ok ((),v)) :
    ∃ packet,
      (liftWG (getTxSkb skb)).run w = .ok (packet,w) ∧
      (liftWG (modifyDev (erasePacketDevice (.inl skb)))).run w = .ok ((),v) ∧
      Packets.epoch v.wg = Packets.epoch w.wg ∧ PacketMaterial.view v.wg skb = none := by
  obtain ⟨device,packet,present,resident,after⟩ := Terminal.native_free skb w v native
  have projections := FirstTerminal.cleanup_views skb w v native
  refine ⟨packet,?_,?_,projections.1,projections.2.1⟩
  · rw [liftWG_run,Packets.getTxSkb_run w.wg w.ambient device skb packet present resident]
    rfl
  · rw [after]
    simp only [liftWG_run,modifyDev,StateT.run_modify,Except.map]
    rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CleanupPrimitive
