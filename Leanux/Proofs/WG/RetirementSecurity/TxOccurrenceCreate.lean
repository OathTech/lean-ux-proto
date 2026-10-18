import Leanux.Proofs.WG.RetirementSecurity.TxOccurrencePublication

/-! The complete native createData caller consumes its unpublished local:
accepted packets become queued occurrences, and rejected packets are freed.
No peer/key funding premise is needed for physical occurrence transport;
the independent key-holder theorem accounts for those references. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes
open Queues.RxCredits

def CreateOccurrences (locals : List TxLocalBatch) (pid : PeerId) (items : List SkbId)
    (ret : Int) (w : WGWorld) : Prop :=
  if ret = 0 ∨ ret = -Leanux.EPIPE then TxInventory locals w
  else TxInventory (⟨.unpublished,pid,items⟩ :: locals) w

theorem TxInventory.publish_return (inventory : TxInventory locals w)
    (items : List SkbId) (ret : Int) (a b : Ambient)
    (run : ((createPublishReturn items ret).run w).run a = .ok ((result,v),b)) :
    result = ret ∧ TxInventory locals v := by
  simp only [createPublishReturn,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨pipe,u,c,branchRun,tail⟩ := run
  have same : u = w := by cases branchRun; rfl
  subst u
  cases pipe with
  | false => simp only [Bool.false_eq_true,ite_false] at tail; cases tail; exact ⟨rfl,inventory⟩
  | true =>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,u,c,publishRun,done⟩ := tail
    cases done
    exact ⟨rfl,inventory.publish items .dead _ b publishRun⟩

theorem TxInventory.create_return
    (inventory : TxInventory (⟨.unpublished,pid,items⟩ :: locals) w)
    (a b : Ambient)
    (run : ((createReturnSource pid items).run w).run a = .ok ((ret,v),b)) :
    CreateOccurrences locals pid items ret v := by
  simp only [createReturnSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,peerRun,dead,t,e,branchRun,tail⟩ := run
  have same := (Origins.getPeer_return pid w u p a c peerRun).1
  subst u
  have same : t = w := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.branch .createDataDead p.isDead) (fun t => t = w))
    w c dead t e rfl branchRun
  subst t
  cases dead with
  | true =>
    simp only [ite_true] at tail
    cases tail
    simpa [CreateOccurrences,Leanux.EINVAL,Leanux.EPIPE] using inventory
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨result,u,c,enqueueRun,publishRun⟩ := tail
    rcases inventory.enqueue_native e c enqueueRun with ⟨refused,hu⟩ | ⟨accepted,hu⟩
    · obtain ⟨returned,hv⟩ := hu.publish_return items result c b publishRun
      simpa [CreateOccurrences,returned,refused,Leanux.ENOSPC,Leanux.EPIPE] using hv
    · obtain ⟨returned,hv⟩ := hu.publish_return items result c b publishRun
      simpa only [CreateOccurrences,returned,ite_eq_left accepted] using hv

theorem TxInventory.cleanup
    (inventory : TxInventory (⟨.unpublished,pid,items⟩ :: locals) w)
    (first : SkbId) (a b : Ambient)
    (run : ((Queues.TxDisposition.cleanupSource pid items first).run w).run a = .ok (((),v),b)) :
    TxInventory locals v := by
  simp only [Queues.TxDisposition.cleanupSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨packet,u,c,readRun,_,t,e,keyRun,_,s,f,peerRun,freeRun⟩ := run
  obtain ⟨same,clock,_,_,_⟩ := Packets.getTxSkb_current first w u packet a c readRun
  subst u
  subst c
  exact (((inventory.key_put (some packet.keypair) false a e keyRun).peer_put
    (some pid) e f peerRun).free_batch f b freeRun).1

theorem create_tail_occurrences (state : CreateOccurrences locals pid items ret w)
    (first : SkbId) (a b : Ambient)
    (run : ((Queues.TxDisposition.createTailSource pid items first ret).run w).run a = .ok (((),v),b)) :
    TxInventory locals v := by
  simp only [Queues.TxDisposition.createTailSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ok,u,c,branchRun,tail⟩ := run
  have guard := (hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (CreateOccurrences locals pid items ret) .createDataOk (ret == 0))
    w a ok u c state branchRun
  cases ok with
  | true =>
    have zero : ret = 0 := by simpa using guard.1.symm
    simp only [ite_true] at tail
    cases tail
    simpa [CreateOccurrences,zero] using guard.2
  | false =>
    have nonzero : ret ≠ 0 := by simpa using guard.1.symm
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨pipe,t,e,branchRun,tail⟩ := tail
    have next := (hoare_iff_run_ambient _ _ _).mp
      (branch_predicate_native (CreateOccurrences locals pid items ret) .createDataOkEpipe
        (ret == -WG.EPIPE)) u c pipe t e guard.2 branchRun
    cases pipe with
    | true =>
      have returned : ret = -Leanux.EPIPE := by simpa [WG.EPIPE,Leanux.EPIPE] using next.1.symm
      simp only [ite_true] at tail
      cases tail
      simpa [CreateOccurrences,returned] using next.2
    | false =>
      have nonpipe : ret ≠ -Leanux.EPIPE := by simpa [WG.EPIPE,Leanux.EPIPE] using next.1.symm
      have saved : TxInventory (⟨.unpublished,pid,items⟩ :: locals) t := by
        simpa [CreateOccurrences,nonzero,nonpipe] using next.2
      simp only [Bool.false_eq_true,ite_false] at tail
      exact saved.cleanup first e b tail

theorem TxInventory.create (inventory : TxInventory (⟨.unpublished,pid,items⟩ :: locals) w)
    (a b : Ambient)
    (run : ((createData pid items).run w).run a = .ok (((),v),b)) : TxInventory locals v := by
  have factor : createData pid items = (do
      let some first := items.head? | invariant "an empty ring item"
      let ret ← createReturnSource pid items
      Queues.TxDisposition.createTailSource pid items first ret) := by
    simp only [Queues.TxDisposition.createSource_factor,createReturnSource,createPublishReturn,
      bind_assoc,bind_if_source,pure_bind]
    rfl
  rw [factor] at run
  cases head : items.head? with
  | none => simp only [head] at run; cases run
  | some first =>
    simp only [head,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨ret,u,c,front,tail⟩ := run
    exact create_tail_occurrences (inventory.create_return a c front) first c b tail

theorem TxInventory.allocate_create (inventory : TxInventory locals w)
    (bounded : Packets.Inv w) (device : w.dev = some d) (pid : PeerId)
    (packets : List DataPacket) (a b : Ambient)
    (run : ((do let items ← packets.mapM newTxSkb; createData pid items).run w).run a =
      .ok (((),v),b)) : TxInventory locals v := by
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨items,u,c,allocateRun,createRun⟩ := run
  exact (inventory.allocate bounded device pid packets a c allocateRun).create c b createRun

end Leanux.Proofs.WG.RetirementSecurity
