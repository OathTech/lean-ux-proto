import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateRepaymentCompletion

/-! A labelled free changes one allocated obligation and one actual cell.
The staged queue projection is exact, while the caller-local owner advances
by that cell; it is never framed as though the freed owner survived. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations QueueHandoff HandshakeSecurity.StagedConservation
set_option pp.structureInstances false

theorem cleanup_birth_quiet (skb : SkbId) (w : World) (history : List CausalJournal.Event) :
    ∃ suffix, (runPrefix (FirstTerminal.cleanupFree skb) w history).2 = history ++ suffix ∧
      ∀ event ∈ suffix, birthPackets event = [] :=
  focused_quiet (TxDisposition.nativeAccess (freeTxSkbPrefix skb)) w history

theorem free_staged (r : Terminal.Receipt) (native : r.Valid) :
    Staged.stagedAt r.run.after.wg = Staged.stagedAt r.run.before.wg := by
  obtain ⟨device,packet,present,_,after⟩ := native.effects
  rw [after]
  funext pid
  simp only [Staged.stagedAt,Packets.update,present,Option.map_some,Option.bind_some]

theorem free_owner (phase : TxLocalPhase)
    (coverage : TxCoverage (⟨phase,pid,skb :: remaining⟩ :: locals) w.wg)
    (inventory : TxInventory (⟨phase,pid,skb :: remaining⟩ :: locals) w.wg)
    (bounded : Packets.Inv w.wg)
    (run : (liftWG (freeTxSkb skb)).run w = .ok ((),v)) :
    TxCoverage (⟨phase,pid,remaining⟩ :: locals) v.wg ∧
      TxInventory (⟨phase,pid,remaining⟩ :: locals) v.wg ∧ Packets.Inv v.wg := by
  have splitCoverage : TxCoverage (⟨phase,pid,[skb]⟩ :: ⟨phase,pid,remaining⟩ :: locals) w.wg := coverage
  have splitInventory : TxInventory (⟨phase,pid,[skb]⟩ :: ⟨phase,pid,remaining⟩ :: locals) w.wg :=
    ⟨inventory.localUnique,inventory.queueUnique,inventory.peersSeparate,
      inventory.localsSeparate,inventory.localResident,inventory.queueResident⟩
  rw [liftWG_run] at run
  cases native : ((freeTxSkb skb).run w.wg).run w.ambient with
  | error reason => simp [native,Except.map] at run
  | ok out =>
    obtain ⟨⟨ignored,g⟩,ambient⟩ := out
    cases ignored
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    have same := congrArg World.wg run.2
    have singleton : ((TxDisposition.freeList [skb]).run w.wg).run w.ambient = .ok (((),g),ambient) := by
      simpa [TxDisposition.freeList,List.forIn_cons,List.forIn_nil,bind_assoc] using native
    exact same ▸ ⟨splitCoverage.free_batch _ _ singleton,
      (splitInventory.free_batch _ _ singleton).1,(Packets.freeTxSkb_facts skb w.wg g _ _ bounded native).1⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
