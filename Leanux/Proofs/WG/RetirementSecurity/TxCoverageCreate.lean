import Leanux.Proofs.WG.RetirementSecurity.TxCoverage
import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceCreate

/-! Native admission moves every allocated TX cell into its peer's logical
queue or removes it at the rejection cleanup. The converse coverage proof
includes EPIPE publication, ENOSPC and dead-peer refusal; it does not assign a
successful socket result to any of those source paths. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes
open Queues.RxCredits

theorem queueContents_of_peers (same : peersAt v=peersAt w) :
    txQueueContents v=txQueueContents w := by
  funext owner
  simpa only [txQueueContents,Queues.RxCredits.handoffTxView,peersAt,Option.bind_map,
    Option.map_bind,Function.comp_def] using
    congrArg (fun cells=>(cells.bind fun table=>table[owner]?.map (·.txQueue.all)).getD []) same

theorem TxCoverage.key_put (before : TxCoverage locals w) (kid : Option KeypairId) (now : Bool)
    (a b : Ambient) (run : ((keypairPut kid now).run w).run a=.ok (((),v),b)) :
    TxCoverage locals v :=
  before.cells ((ProjectedAction.iff_run_ambient _ _ _).mp
    (Queues.TxDisposition.keyPut_packets kid now) w a () v b run)
    (queueContents_of_peers (put_peers kid now w v a b run))

theorem TxCoverage.peer_put (before : TxCoverage locals w) (pid : Option PeerId)
    (a b : Ambient) (run : ((peerPut pid).run w).run a=.ok (((),v),b)) :
    TxCoverage locals v :=
  before.cells ((ProjectedAction.iff_run_ambient _ _ _).mp
    (Queues.TxDisposition.peerPut_packets pid) w a () v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (queueContents_peer_put pid) w a () v b run)

theorem TxCoverage.publish (before : TxCoverage locals w) (items : List SkbId)
    (state : PacketState) (a b : Ambient)
    (run : ((enqueuePerPeerTx items state).run w).run a=.ok (((),v),b)) :
    TxCoverage locals v := by
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Queues.TxDisposition.publication_queues items state) w a () v b run
  apply before.frame ((ProjectedAction.iff_run_ambient _ _ _).mp
    (publish_tx_present items state) w a () v b run)
  funext owner
  simpa only [txQueueContents,Queues.RxCredits.handoffTxView,Queues.TxDisposition.txQueues,
    PeerBorrow.resident,wgStoreView,Option.map_bind,Option.map_map,Function.comp_def] using
    congrArg (fun cells=>((cells owner).map (·.all)).getD []) queues

theorem TxCoverage.enqueue_native
    (inventory : TxCoverage (⟨.unpublished,pid,items⟩ :: locals) w)
    (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid items).run w).run a = .ok ((ret,v),b)) :
    (ret = -Leanux.ENOSPC ∧ TxCoverage (⟨.unpublished,pid,items⟩ :: locals) v) ∨
      ((ret = 0 ∨ ret = -Leanux.EPIPE) ∧ TxCoverage locals v) := by
  rw [Queues.RxCredits.enqueue_factor] at run
  cases head : items.head? with
  | none => simp only [head] at run; cases run
  | some first =>
    simp only [head,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨_,u,c,markRun,p,t,e,peerRun,full,s,f,branchRun,tail⟩ := run
    have marked := (ProjectedAction.iff_run_ambient _ _ _).mp
      (ownershipPoints_holderStore _
        (setTx_holderStore first (fun p => {p with state := .uncrypted}) (fun _ => rfl)))
      w a () u c markRun
    have hu := inventory.points marked
    obtain ⟨same,_,d,device,found⟩ := Origins.getPeer_return pid u t p c e peerRun
    subst t
    have same : s = u := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.branch .enqueuePeerQueueFull
        (decide (p.txQueue.count ≥ MAX_QUEUED_PACKETS))) (fun s => s = u))
      u e full s f rfl branchRun
    subst s
    cases full with
    | true =>
      simp only [ite_true] at tail
      cases tail
      exact Or.inl ⟨rfl,hu⟩
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨_,s,g,installRun,tailRun⟩ := tail
      have installed : replacePeer u d pid {p with txQueue := p.txQueue.enqueue items} = s ∧ f = g := by
        simpa [setPeer,modifyDev,replacePeer,device] using installRun
      have hs : TxCoverage locals s := installed.1 ▸ hu.enqueue device found
      exact Or.inr ⟨enqueue_tail_result items g b tailRun,
        hs.points ((ProjectedAction.iff_run_ambient _ _ _).mp (enqueue_tail_ownership items)
          s g ret v b tailRun)⟩

def CreateCoverage (locals : List TxLocalBatch) (pid : PeerId) (items : List SkbId)
    (ret : Int) (w : WGWorld) : Prop :=
  if ret = 0 ∨ ret = -Leanux.EPIPE then TxCoverage locals w
  else TxCoverage (⟨.unpublished,pid,items⟩ :: locals) w

theorem TxCoverage.publish_return (inventory : TxCoverage locals w)
    (items : List SkbId) (ret : Int) (a b : Ambient)
    (run : ((createPublishReturn items ret).run w).run a = .ok ((result,v),b)) :
    result = ret ∧ TxCoverage locals v := by
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

theorem TxCoverage.create_return
    (inventory : TxCoverage (⟨.unpublished,pid,items⟩ :: locals) w)
    (a b : Ambient)
    (run : ((createReturnSource pid items).run w).run a = .ok ((ret,v),b)) :
    CreateCoverage locals pid items ret v := by
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
    simpa [CreateCoverage,Leanux.EINVAL,Leanux.EPIPE] using inventory
  | false =>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨result,u,c,enqueueRun,publishRun⟩ := tail
    rcases inventory.enqueue_native e c enqueueRun with ⟨refused,hu⟩ | ⟨accepted,hu⟩
    · obtain ⟨returned,hv⟩ := hu.publish_return items result c b publishRun
      simpa [CreateCoverage,returned,refused,Leanux.ENOSPC,Leanux.EPIPE] using hv
    · obtain ⟨returned,hv⟩ := hu.publish_return items result c b publishRun
      simpa only [CreateCoverage,returned,ite_eq_left accepted] using hv

theorem TxCoverage.cleanup
    (inventory : TxCoverage (⟨.unpublished,pid,items⟩ :: locals) w)
    (first : SkbId) (a b : Ambient)
    (run : ((Queues.TxDisposition.cleanupSource pid items first).run w).run a = .ok (((),v),b)) :
    TxCoverage locals v := by
  simp only [Queues.TxDisposition.cleanupSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨packet,u,c,readRun,_,t,e,keyRun,_,s,f,peerRun,freeRun⟩ := run
  obtain ⟨same,clock,_,_,_⟩ := Packets.getTxSkb_current first w u packet a c readRun
  subst u
  subst c
  exact (((inventory.key_put (some packet.keypair) false a e keyRun).peer_put
    (some pid) e f peerRun).free_batch f b freeRun)

theorem create_tail_coverage (state : CreateCoverage locals pid items ret w)
    (first : SkbId) (a b : Ambient)
    (run : ((Queues.TxDisposition.createTailSource pid items first ret).run w).run a = .ok (((),v),b)) :
    TxCoverage locals v := by
  simp only [Queues.TxDisposition.createTailSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ok,u,c,branchRun,tail⟩ := run
  have guard := (hoare_iff_run_ambient _ _ _).mp
    (branch_predicate_native (CreateCoverage locals pid items ret) .createDataOk (ret == 0))
    w a ok u c state branchRun
  cases ok with
  | true =>
    have zero : ret = 0 := by simpa using guard.1.symm
    simp only [ite_true] at tail
    cases tail
    simpa [CreateCoverage,zero] using guard.2
  | false =>
    have nonzero : ret ≠ 0 := by simpa using guard.1.symm
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨pipe,t,e,branchRun,tail⟩ := tail
    have next := (hoare_iff_run_ambient _ _ _).mp
      (branch_predicate_native (CreateCoverage locals pid items ret) .createDataOkEpipe
        (ret == -WG.EPIPE)) u c pipe t e guard.2 branchRun
    cases pipe with
    | true =>
      have returned : ret = -Leanux.EPIPE := by simpa [WG.EPIPE,Leanux.EPIPE] using next.1.symm
      simp only [ite_true] at tail
      cases tail
      simpa [CreateCoverage,returned] using next.2
    | false =>
      have nonpipe : ret ≠ -Leanux.EPIPE := by simpa [WG.EPIPE,Leanux.EPIPE] using next.1.symm
      have saved : TxCoverage (⟨.unpublished,pid,items⟩ :: locals) t := by
        simpa [CreateCoverage,nonzero,nonpipe] using next.2
      simp only [Bool.false_eq_true,ite_false] at tail
      exact saved.cleanup first e b tail

theorem TxCoverage.create (inventory : TxCoverage (⟨.unpublished,pid,items⟩ :: locals) w)
    (a b : Ambient)
    (run : ((createData pid items).run w).run a = .ok (((),v),b)) : TxCoverage locals v := by
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
    exact create_tail_coverage (inventory.create_return a c front) first c b tail

theorem TxCoverage.allocate_create (inventory : TxCoverage locals w)
    (pid : PeerId)
    (packets : List DataPacket) (a b : Ambient)
    (run : ((do let items ← packets.mapM newTxSkb; createData pid items).run w).run a =
      .ok (((),v),b)) : TxCoverage locals v := by
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨items,u,c,allocateRun,createRun⟩ := run
  exact (inventory.allocate pid packets a c allocateRun).create c b createRun

end Leanux.Proofs.WG.RetirementSecurity
