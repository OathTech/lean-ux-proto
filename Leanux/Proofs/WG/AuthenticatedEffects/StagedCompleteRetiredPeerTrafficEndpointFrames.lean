import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTrafficFinishFrames

/-! The native traffic relations choose the very same RX ledger for the
inherited ownership facts and the exact peer account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Traffic
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders

theorem inject_outcome
    (actors : ∀ initial before,Scheduler.Actors initial loans before)
    (hi : Outer.Inv cs loans h w)
    (outcome : InjectAccount.Outcome cs admitted family port msg tos ll dest w v h k result) :
    ExactBoundary [] loans v.wg := by
  obtain ⟨src,u,t,j,start,step,done⟩ := outcome
  have front := Outer.store hi (InjectAccount.front_store start)
  have entry := Outer.to_aux front (InjectAccount.front_present start)
  have after := Auxiliary.section_at_cut entry step
  obtain ⟨_,_,_,_,_,_,post,_,_⟩ := inject_finish (actors admitted j) after done
  have exactAccount := post.residual (List.append_nil k).symm
  simpa only [NapiCarrier.removedPackets,remaining,List.filter_nil] using exactAccount

theorem inject_normal
    (actors : ∀ initial before,Scheduler.Actors initial loans before)
    (hi : Outer.Inv cs loans h w)
    (run : runPrefix (RxHistory.inject family port msg tos ll dest) w h=(.ok (result,v),k)) :
    ∃ admitted,InjectAccount.Outcome cs admitted family port msg tos ll dest w v h k result ∧
      Outer.Inv [] loans k v ∧ result=(msg.length : Int) ∧
      (∀ (d : Device) (id : SkbId) (packet : RxPacket),v.wg.dev=some d→d.rxSkbs[id]?≠some packet) := by
  obtain ⟨admitted,outcome,entry,length,empty⟩ := HolderTrafficEntry.inject_normal hi.1 run
  exact ⟨admitted,outcome,⟨entry,inject_outcome actors hi outcome⟩,length,empty⟩

theorem flood_outcome
    (actors : ∀ initial before,Scheduler.Actors initial loans before)
    (hi : Outer.Inv cs loans h w)
    (outcome : FloodAccount.Outcome cs next count port family input w v h k result) :
    ExactBoundary next loans v.wg := by
  obtain ⟨src,u,t,j,middle,suffix,start,path,done,history,rfl⟩ := outcome
  have front := Outer.store hi (FloodAccount.front_store start)
  have entry := Outer.to_aux front (FloodAccount.front_present start)
  have after := flood_path_restore entry path
  have post := (flood_finish (actors middle j) t j after).choose_spec.2.2
  rw [done] at post
  exact post.residual history

theorem flood_normal
    (actors : ∀ initial before,Scheduler.Actors initial loans before)
    (hi : Outer.Inv cs loans h w)
    (run : runPrefix (RxHistory.flood count port family input) w h=(.ok (result,v),k)) :
    ∃ next,FloodAccount.Outcome cs next count port family input w v h k result ∧
      Outer.Inv next loans k v := by
  obtain ⟨next,outcome,entry⟩ := HolderTrafficEntry.flood_normal hi.1 run
  exact ⟨next,outcome,entry,flood_outcome actors hi outcome⟩

theorem batch_outcome
    (actors : ∀ initial before,Scheduler.Actors initial loans before)
    (hi : Outer.Inv cs loans h w)
    (outcome : BatchAccount.Outcome cs next entries w v h k result) :
    ExactBoundary next loans v.wg := by
  obtain ⟨d,cqes,u,t,j,middle,suffix,start,path,done,history,rfl⟩ := outcome
  have front := Outer.store hi (BatchAccount.front_store start)
  have entry := Outer.to_aux front (BatchAccount.front_present start)
  have after := batch_path_restore entry path
  have post := (batch_finish (actors middle j) entries cqes t j after).choose_spec.2.2
  rw [done] at post
  exact post.residual history

theorem batch_normal
    (actors : ∀ initial before,Scheduler.Actors initial loans before)
    (hi : Outer.Inv cs loans h w)
    (run : runPrefix (RxHistory.batch entries) w h=(.ok (result,v),k)) :
    ∃ next,BatchAccount.Outcome cs next entries w v h k result ∧ Outer.Inv next loans k v := by
  obtain ⟨next,outcome,entry⟩ := HolderTrafficEntry.batch_normal entries hi.1 run
  exact ⟨next,outcome,entry,batch_outcome actors hi outcome⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Traffic
