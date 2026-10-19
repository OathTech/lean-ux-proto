import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionFreeFrames

/-! The actual free callback is total from its selected local and consumes
that cell's exact cleanup debt. It cannot revise a terminal outcome or delete
another remaining binding's debt. No callback or reachability premise is used. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CompletionCuts

theorem free_checked (context : Context) (skb : SkbId) (remaining : List SkbId) :
    Ensures (State context (.freeing (skb :: remaining))) (Stopped context)
      (FirstTerminal.cleanupFree skb) (fun _ => State context (.freeing remaining)) := by
  intro w history before
  obtain ⟨packet,resident⟩ := State.resident (skb := skb) before (by simp [Phase.active])
  obtain ⟨v,native⟩ := native_free_total resident
  have appends : Appends (FirstTerminal.cleanupFree skb) := Appends.focus _ _ _
  obtain ⟨suffix,grown⟩ := appends w history
  have run : runPrefix (FirstTerminal.cleanupFree skb) w history = (.ok ((),v),history ++ suffix) :=
    Prod.ext ((FirstTerminal.cleanupFree_erases skb w history).trans native) grown
  rw [run]
  refine ⟨suffix,rfl,?_⟩
  obtain ⟨ledger,debts,step,support,recorded,tail,assigned,coverage,inventory⟩ := before
  have distinct : (skb :: remaining).Nodup := (List.nodup_append.mp inventory.localUnique).1
  have inItems : skb ∈ context.items := by
    obtain ⟨left,equal⟩ := tail
    rw [← equal]
    simp [Phase.remaining]
  obtain ⟨binding,member,same⟩ := List.mem_map.mp inItems
  have bound : binding.skb ∈ skb :: remaining := by simp [same]
  obtain ⟨outcome,debt,terminal⟩ := (assigned binding member).2 bound
  let chosen : CleanupDebt := ⟨binding.ticket,binding.position,binding.ordinal,outcome⟩
  have origin : Origin history chosen.position chosen.ordinal binding.generation skb binding.value := by
    simpa only [Binding.recorded,chosen,same] using recorded binding member
  have epoch := ((support.cleanup chosen debt).2.at_origin origin).1
  obtain ⟨_,after,_,_,_⟩ := FirstTerminal.cleanup_debt skb w v history suffix run support chosen debt origin epoch
  obtain ⟨coverageAfter,inventoryAfter⟩ := free_ownership coverage inventory native
  refine ⟨ledger,forgetFreedCell history binding.generation skb debts,step,after,
    fun b inside => (recorded b inside).append suffix,?_,?_,coverageAfter,inventoryAfter⟩
  · obtain ⟨left,equal⟩ := tail
    exact ⟨left ++ [skb],by simpa only [Phase.remaining,List.append_assoc,List.singleton_append] using equal⟩
  · intro b inside
    refine ⟨(assigned b inside).1,?_⟩
    intro still
    obtain ⟨result,old,settled⟩ := (assigned b inside).2 (List.mem_cons_of_mem skb still)
    refine ⟨result,mem_forgetFreedCell.mpr ⟨old,?_⟩,settled⟩
    rintro ⟨_,other⟩
    have equal : b.skb = skb := ((recorded b inside).unique other).2.1
    exact (List.nodup_cons.mp distinct).1 (equal ▸ still)

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
