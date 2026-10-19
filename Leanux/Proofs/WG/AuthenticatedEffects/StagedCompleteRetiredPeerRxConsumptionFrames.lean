import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxConsumption

/-! Whole native receive composition preserves the exact peer-reference
account and its source-selected carrier, under the existing packet and
physical-ring invariants. No assumed readiness or successful enqueue occurs. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem Account.consume_data (account : Account holders carriers loans w) (fresh : Packets.Inv w)
    (physical : NativeRxInv epoch (PtrRing.init n) history w) (a b : Ambient)
    (run : ((consumeData msg src ds).run w).run a = .ok (((),v),b)) :
    ∃ receipt, ExactConsumption holders carriers loans msg src ds w v a b receipt := by
  rw [←RxOrigin.consumeSource_eq] at run
  unfold RxOrigin.consumeSource RxOrigin.consumeWith at run
  obtain ⟨result,middle,aa,admissionRun,finish⟩ := (by simpa only [MaterialOrigin.bind_ok_ambient] using run)
  refine ⟨⟨result,w,middle,a,aa⟩,rfl,rfl,admissionRun,?_⟩
  cases result with
  | none =>
    have eq : middle = v ∧ aa = b := by simpa using finish
    rcases eq with ⟨rfl,rfl⟩
    exact ⟨rfl,rfl,account.admit_none _ _ admissionRun⟩
  | some ctx =>
    obtain ⟨owner,admittedAccount,stable,slot,word,admitted⟩ := account.admit_some fresh a aa admissionRun
    have ring : NativeRxInv epoch (PtrRing.init n) history middle := by
      obtain ⟨ring,refines,cell⟩ := physical
      exact ⟨ring,refines,((ProjectedAction.iff_run_ambient _ _ _).mp
        (admit_ring msg src ds) w a _ middle aa admissionRun).trans cell⟩
    obtain ⟨_,pkt,stored,_⟩ := admittedAccount.funded.carriers.inventory.present
      ⟨⟨owner.epoch,ctx.slot⟩,owner,.unpublished⟩ (by simp)
    have eq : pkt = ctx.packet := admitted_packet a aa admissionRun stored
    subst pkt
    have state : ctx.packet.state = .uncrypted := by
      obtain ⟨entry,a1,t1,a2,t2,a3,t3,peer,a4,t4,a5,t5,_,_,_,_,_,packet,_⟩ := admitted
      rw [packet]
    exact ⟨owner,admittedAccount,stable,slot,word,admitted,
      admittedAccount.rx_finish_boundary stable ctx rfl rfl stored slot.symm state ring aa b finish⟩

theorem ExactConsumption.lower
    (receipt : ExactConsumption holders carriers loans msg src ds w v a b r) :
    StableConsumption carriers (holders.owners ++ loans) msg src ds w v a b r := by
  obtain ⟨before,ambient,valid,rest⟩ := receipt
  refine ⟨before,ambient,valid,?_⟩
  cases value : r.value with
  | none =>
    simp only [value] at rest ⊢
    exact ⟨rest.1,rest.2.1,rest.2.2.funded.carriers,rest.2.2.stable⟩
  | some ctx =>
    simp only [value] at rest ⊢
    obtain ⟨owner,account,_,slot,word,admitted,ret,middle,aa,enqueue,finish,choices,after⟩ := rest
    refine ⟨owner,account.funded.carriers,slot,word,admitted,ret,middle,aa,enqueue,finish,choices,?_⟩
    by_cases full : ret = -ENOSPC <;> simp only [full,ite_eq_left,ite_false] at after ⊢
    · exact ⟨after.1.funded.carriers,after.1.stable,after.2⟩
    · exact ⟨after.funded.carriers,after.stable⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
