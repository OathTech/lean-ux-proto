import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedFrames
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionFree

/-! Ordinary completion free is total from the actual selected local. It
removes precisely that cell's cleanup debt while retaining the canonical
ledger, source provenance and staged queues. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity HandshakeSecurity.StagedConservation

theorem free_entry_facts (before : Packets.Inv w.wg)
    (native : (liftWG (freeTxSkb skb)).run w = .ok ((),v)) :
    Packets.Inv v.wg ∧ Staged.stagedAt v.wg = Staged.stagedAt w.wg := by
  obtain ⟨device,packet,atDevice,cell,after⟩ := Terminal.native_free skb w v native
  have performed := Packets.freeTxSkb_run w.wg w.ambient device skb packet atDevice cell
  have bounded := (Packets.freeTxSkb_facts skb _ _ _ _ before performed).1
  rw [after]
  exact ⟨bounded,by funext pid; simp [Staged.stagedAt,Packets.update,atDevice]⟩

/-- The native free yields an explicit successor debt list for the same
canonical ledger. No terminal receipt or label is invented at cleanup. -/
theorem indexed_free_total
    (before : Owned context (.freeing (skb :: rest)) history ledger debts w) :
    ∃ v suffix generation,
      runPrefix (FirstTerminal.cleanupFree skb) w history = (.ok ((),v),history ++ suffix) ∧
      Owned context (.freeing rest) (history ++ suffix) ledger
        (forgetFreedCell history generation skb debts) v := by
  obtain ⟨packet,resident⟩ := before.state.resident (skb := skb) (by simp [Phase.active])
  obtain ⟨v,native⟩ := native_free_total resident
  have appends : Appends (FirstTerminal.cleanupFree skb) := Appends.focus _ _ _
  obtain ⟨suffix,grown⟩ := appends w history
  have run : runPrefix (FirstTerminal.cleanupFree skb) w history = (.ok ((),v),history ++ suffix) :=
    Prod.ext ((FirstTerminal.cleanupFree_erases skb w history).trans native) grown
  have birthEq : births (history ++ suffix) = births history := by
    have same := focus_births CausalJournal.txEvent CausalJournal.txEvent? (fun _ => rfl)
      (TxDisposition.nativeAccess (freeTxSkbPrefix skb)) w history
    change births (runPrefix (FirstTerminal.cleanupFree skb) w history).2 = births history at same
    rw [grown] at same
    exact same
  have distinct : (skb :: rest).Nodup := (List.nodup_append.mp before.entry.inventory.localUnique).1
  have inItems : skb ∈ context.items := by
    obtain ⟨left,equal⟩ := before.cursor.remaining
    rw [← equal]
    simp [Phase.remaining]
  obtain ⟨binding,member,same⟩ := List.mem_map.mp inItems
  have bound : binding.skb ∈ skb :: rest := by simp [same]
  obtain ⟨outcome,debt,terminal⟩ := (before.cursor.assigned binding member).2 bound
  let chosen : CleanupDebt := ⟨binding.ticket,binding.position,binding.ordinal,outcome⟩
  have origin : Origin history chosen.position chosen.ordinal binding.generation skb binding.value := by
    simpa only [Binding.recorded,chosen,same] using before.cursor.recorded binding member
  have support : FirstTerminal.Support (births history) history ledger debts w.wg :=
    ⟨before.entry.core.physical,before.entry.core.valid⟩
  have epoch := ((support.cleanup chosen debt).2.at_origin origin).1
  obtain ⟨_,after,_,_,_⟩ := FirstTerminal.cleanup_debt skb w v history suffix run support chosen debt origin epoch
  obtain ⟨coverage,inventory⟩ := free_ownership before.entry.coverage before.entry.inventory native
  obtain ⟨bounded,queues⟩ := free_entry_facts before.entry.packets native
  have keptEpoch := (native_free_views skb w v native).1
  refine ⟨v,suffix,binding.generation,run,⟨⟨before.cursor.step,?_,?_,?_⟩,?_,
    birthEq.trans before.domain⟩⟩
  · exact fun b inside => (before.cursor.recorded b inside).append suffix
  · obtain ⟨left,equal⟩ := before.cursor.remaining
    exact ⟨left ++ [skb],by simpa only [Phase.remaining,List.append_assoc,List.singleton_append] using equal⟩
  · intro b inside
    refine ⟨(before.cursor.assigned b inside).1,?_⟩
    intro still
    obtain ⟨result,old,settled⟩ := (before.cursor.assigned b inside).2 (List.mem_cons_of_mem skb still)
    refine ⟨result,mem_forgetFreedCell.mpr ⟨old,?_⟩,settled⟩
    rintro ⟨_,other⟩
    have equal : b.skb = skb := ((before.cursor.recorded b inside).unique other).2.1
    exact (List.nodup_cons.mp distinct).1 (equal ▸ still)
  · refine ⟨⟨?_,before.entry.core.queues.views_append suffix keptEpoch queues,
      before.entry.core.selected.append suffix,after.toPhysical⟩,
      before.entry.justified.append suffix,before.entry.allocationLinks.append suffix,
      before.entry.noSelected,bounded,coverage,inventory⟩
    rw [birthEq]
    exact before.entry.core.valid

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
