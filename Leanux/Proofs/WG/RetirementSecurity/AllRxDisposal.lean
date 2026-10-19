import Leanux.Proofs.WG.RetirementSecurity.ConditionalRetirementRx

/-! The literal receive-poll release suffix is shared by DEAD, rejected and
authenticated packets. Successful authentication changes the free flag, not
the key payment; final removal depends on the count at this actual source cut. -/
namespace Leanux.Proofs.WG.RetirementSecurity.AllRxDisposal
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem final_reference (id : SkbId) (pkt : RxPacket) (flag : Bool)
    (found : keyAt w pkt.keypair=some k) (last : k.refcount=1) (a b : Ambient)
    (run : ((cleanup id pkt flag).run w).run a=.ok (((),v),b)) :
    keyAt v pkt.keypair=none := by
  simp only [cleanup,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨r,u,c,putRun,r2,t,e,peerRun,_,s,f,branchRun,freeRun⟩ := run
  cases r
  cases r2
  have erased := (FinalDisposal.put_one found last false a c putRun).1
  have absent := FinalDisposal.absent_retains erased (peerPut_retains (some pkt.peer) u t c e peerRun)
  have same : s=t := by cases branchRun; rfl
  subst s
  exact ((ProjectedAction.iff_run_ambient _ _ _).mp
    (FinalDisposal.packet_key (SkbStore.freeRx id) pkt.keypair) t f () v b freeRun).trans absent

/-- This is the original suffix for every receive branch. In the accepted
AEAD/replay/endpoint path flag is false; DEAD or rejection uses true. -/
theorem poll_suffix (pid id : Nat) (pkt : RxPacket) (flag : Bool) (owner : pkt.peer=pid)
    (found : keyAt w pkt.keypair=some k) (last : k.refcount=1) (a b : Ambient)
    (run : ((do
      keypairPut (some pkt.keypair) false
      peerPut (some pid)
      _←branch .rxPollFree flag
      freeRxSkb id : WG.M Unit).run w).run a=.ok (((),v),b)) :
    keyAt v pkt.keypair=none := by
  apply final_reference id pkt flag found last a b
  rwa [cleanup_poll_guard id pkt pid flag owner]

end Leanux.Proofs.WG.RetirementSecurity.AllRxDisposal
