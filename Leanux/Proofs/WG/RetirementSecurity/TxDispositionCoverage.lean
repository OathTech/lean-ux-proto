import Leanux.Proofs.WG.RetirementSecurity.TxCryptSendFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceQueueContents

/-! Exact native TX-worker disposal. A normal iteration either retains all
packet cells and logical queues, or removes exactly the selected owning batch
and its cells. Socket completion is a separate source cut; this theorem does
not infer a send from deletion or identify equal staged packet values. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxDispositionCoverage
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

def Erased (items : List SkbId) (w v : WGWorld) : Prop :=
  TxDisposition.txPackets v = fun id=>if id∈items then none else TxDisposition.txPackets w id

theorem step_ring (pid : PeerId) : SameView TxRing.nativeCell (txStep pid) := by
  intro initial
  let P := fun w=>TxRing.nativeCell w=initial
  have read (peer : PeerId) : Preserves P (getPeer peer) := (TxRing.getPeer_frame peer).wp (·=initial)
  have write (peer : PeerId) (value : Peer) : Preserves P (setPeer peer value) :=
    (TxRing.setPeer_frame peer value).wp (·=initial)
  have packet (id : SkbId) : Preserves P (getTxSkb id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a value v b before run
    exact (Packets.getTxSkb_current id w v value a b run).1 ▸ before
  have free (id : SkbId) : Preserves P (freeTxSkb id) := by
    unfold freeTxSkb
    apply hoare_liftSkb
    intro w d store before device
    simpa only [P,TxRing.nativeCell,device,Option.map_some] using before
  have key (kid : Option KeypairId) (now : Bool) : Preserves P (keypairPut kid now) :=
    (TxRing.keypairPut_frame kid now).wp (·=initial)
  have peer (owner : Option PeerId) : Preserves P (peerPut owner) :=
    (TxRing.peerPut_frame owner).wp (·=initial)
  have complete (owner : PeerId) (items : List SkbId) : Preserves P (createDataDone owner items) :=
    ((createDataDone_cryptWire owner items).factor Prod.fst).wp (·=initial)
  have peek (queue : PrevQueue (List SkbId)) : Preserves P queue.peek :=
    ((cryptWire_store (prevQueuePeek_sameWGStore queue)).factor Prod.fst).wp (·=initial)
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : WG.M α) :=
    hoare_liftAmbient action P
  change Preserves P _
  routing_tx_source [txStep] using [read,write,packet,free,key,peer,complete,peek,ambient]

/-- The successful worker retains the actual device epoch and therefore each
slot's lifetime allocation stamp throughout this native source call. -/
theorem step_stamp (pid : PeerId) (id : SkbId) (a b : Ambient)
    (run : ((txStep pid).run w).run a=.ok ((result,v),b)) :
    packetStamp v id=packetStamp w id := by
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp (step_ring pid) w a result v b run
  have epoch := congrArg (fun cell : Option (Nat × PtrRing (List SkbId))=>
    (cell.map Prod.fst).getD 0) same
  simpa only [packetStamp,TxRing.nativeCell,Option.map_map,Function.comp_def] using
    congrArg (fun epoch=>(epoch,id+1)) epoch

theorem free_live (id : SkbId) (a b : Ambient)
    (run : ((freeTxSkb id).run w).run a=.ok (((),v),b)) :
    ∃packet,TxDisposition.txPackets w id=some packet := by
  cases device : w.dev with
  | none => simp [freeTxSkb,liftSkb_run,device] at run
  | some d =>
    cases stored : d.txSkbs[id]? with
    | none =>
      simp [freeTxSkb,liftSkb_run,SkbStore.freeTx,SkbStore.getTx,device,stored,
        invariant,AmbientM.invariant] at run
      cases run
    | some packet => exact ⟨packet,by simp [TxDisposition.txPackets,device,stored]⟩

/-- A normal complete free traversal cannot contain a duplicate or an absent
packet. An attempted second free instead Stops at its actual getter. -/
theorem free_list_live (items : List SkbId) (a b : Ambient)
    (run : ((TxDisposition.freeList items).run w).run a=.ok (((),v),b)) :
    items.Nodup ∧ ∀id∈items,∃packet,TxDisposition.txPackets w id=some packet := by
  induction items generalizing w a with
  | nil => exact ⟨by simp,by simp⟩
  | cons id rest ih =>
    rw [TxDisposition.freeList_cons,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨_,u,c,freed,tail⟩:=run
    obtain ⟨packet,stored⟩:=free_live id a c freed
    obtain ⟨unique,resident⟩:=ih c tail
    have cells := (hoare_iff_run_ambient _ _ _).mp
      (TxDisposition.free_packet_wp id (TxDisposition.txPackets w)) w a () u c rfl freed
    have absent : id∉rest := by
      intro member
      obtain ⟨pkt,found⟩:=resident id member
      simp [cells] at found
    refine ⟨List.nodup_cons.mpr ⟨absent,unique⟩,?_⟩
    intro other member
    rcases List.mem_cons.mp member with same | remaining
    · subst other; exact ⟨packet,stored⟩
    · obtain ⟨pkt,found⟩:=resident other remaining
      have different : id≠other := by intro same; subst other; exact absent remaining
      exact ⟨pkt,by simpa [cells,different] using found⟩

theorem dispose_live (pid : PeerId) (items : List SkbId) (kid : KeypairId) (a b : Ambient)
    (run : ((TxDisposition.disposeSource pid items kid).run w).run a=.ok ((result,v),b)) :
    items.Nodup ∧ ∀id∈items,∃packet,TxDisposition.txPackets w id=some packet := by
  have factor : TxDisposition.disposeSource pid items kid=(do
      TxDisposition.freeList items
      keypairPut (some kid) false
      peerPut (some pid)
      pure true) := by simp [TxDisposition.disposeSource,TxDisposition.freeList]
  rw [factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,freed,_⟩:=run
  exact free_list_live items a c freed

theorem dispose (pid : PeerId) (items : List SkbId) (kid : KeypairId) (a b : Ambient)
    (run : ((TxDisposition.disposeSource pid items kid).run w).run a=.ok ((result,v),b)) :
    result=true ∧ Erased items w v ∧ txQueueContents v=txQueueContents w := by
  have factor : TxDisposition.disposeSource pid items kid=(do
      TxDisposition.freeList items
      keypairPut (some kid) false
      peerPut (some pid)
      pure true) := by simp [TxDisposition.disposeSource,TxDisposition.freeList]
  rw [factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,freed,_,t,e,paid,_,s,f,released,done⟩:=run
  cases done
  have cells := (hoare_iff_run_ambient _ _ _).mp
    (TxDisposition.freeList_wp items (TxDisposition.txPackets w)) w a () u c rfl freed
  have keyCells := (ProjectedAction.iff_run_ambient _ _ _).mp
    (TxDisposition.keyPut_packets (some kid) false) u c () t e paid
  have peerCells := (ProjectedAction.iff_run_ambient _ _ _).mp
    (TxDisposition.peerPut_packets (some pid)) t e () v b released
  have freePeers := (ProjectedAction.iff_run_ambient _ _ _).mp
    (free_list_peer_frame items) w a () u c freed
  have keyPeers := put_peers (some kid) false u t c e paid
  have peersContents {x y : WGWorld} (same : peersAt x=peersAt y) :
      txQueueContents x=txQueueContents y := by
    funext owner
    simpa only [txQueueContents,RxCredits.handoffTxView,peersAt,Option.bind_map,Option.map_bind,Function.comp_def]
      using congrArg (fun peers=>(peers.bind fun table=>table[owner]?.map (·.txQueue.all)).getD []) same
  exact ⟨rfl,peerCells.trans (keyCells.trans cells),
    ((ProjectedAction.iff_run_ambient _ _ _).mp (queueContents_peer_put (some pid))
      t e () v b released).trans ((peersContents keyPeers).trans (peersContents freePeers))⟩

theorem completion (pid : PeerId) (items : List SkbId) (head : DataPacket) :
    SameView (fun w=>(TxDisposition.txPackets w,txQueueContents w)) (txCompletionSource pid items head) := by
  unfold txCompletionSource
  apply SameView.bind (show SameView (fun w=>(TxDisposition.txPackets w,txQueueContents w))
    (branch .txCrypted (head.state == .crypted)) from by
      apply (ProjectedAction.iff_run_ambient _ _ _).mpr
      intro w a result v b run
      cases run
      rfl)
  intro crypted
  split
  · exact ((createDataDone_cryptWire pid items).factor Prod.snd).product
      ((RxCredits.TxReservation.createDataDone_queues pid items).factor (fun queues pid=>(queues pid).getD []))
  · exact SameView.pure _ _

theorem drop (pid : PeerId) (a b : Ambient)
    (run : ((txDropSource pid).run w).run a=.ok (((),v),b)) :
    TxDisposition.txPackets v=TxDisposition.txPackets w ∧
      txQueueContents v=fun owner=>if owner=pid then
        ((peerAt w pid).map fun p=>p.txQueue.dropPeeked.all).getD [] else txQueueContents w owner := by
  obtain ⟨d,p,device,stored,_,after⟩:=txDrop_effect pid a b run
  refine ⟨?_,?_⟩
  · funext id
    simp [TxDisposition.txPackets,after,replacePeer,device]
  · funext owner
    by_cases same : owner=pid
    · subst owner
      simp [txQueueContents,RxCredits.handoffTxView,peerAt,after,replacePeer,device,stored]
    · simp [txQueueContents,RxCredits.handoffTxView,after,replacePeer,device,
        same,Ne.symm same,Std.TreeMap.getElem?_insert]

theorem ready_tail (pid : PeerId) (a b : Ambient)
    (cached : ∀p,peerAt w pid=some p→p.txQueue.peeked=first)
    (run : ((txReadyTail pid first).run w).run a=.ok ((result,v),b)) :
    ∃ items headId head, first=some items ∧ items.head?=some headId ∧
      TxDisposition.txPackets w headId=some head ∧ result=true ∧ items.Nodup ∧ Erased items w v ∧
      txQueueContents v=fun owner=>if owner=pid then (txQueueContents w pid).tail else txQueueContents w owner := by
  cases first with
  | none => simp only [txReadyTail] at run; cases run
  | some items =>
    cases headId : items.head? with
    | none => simp only [txReadyTail,headId] at run; cases run
    | some id =>
      rw [txReadyTail_factor pid items id headId,MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨head,u,c,read,tail⟩:=run
      obtain ⟨same,clock,d,device,stored⟩:=Packets.getTxSkb_current id w u head a c read
      subst u
      subst c
      rw [MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨_,dropped,e,droppedRun,tail⟩:=tail
      rw [MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨_,completed,f,completedRun,disposedRun⟩:=tail
      obtain ⟨dropCells,dropQueues⟩:=drop pid a e droppedRun
      have kept := (ProjectedAction.iff_run_ambient _ _ _).mp
        (completion pid items head) dropped e () completed f completedRun
      have keptCells : TxDisposition.txPackets completed=TxDisposition.txPackets dropped:=congrArg Prod.fst kept
      have keptQueues : txQueueContents completed=txQueueContents dropped:=congrArg Prod.snd kept
      obtain ⟨finished,erased,queues⟩:=dispose pid items head.keypair f b disposedRun
      have unique := (dispose_live pid items head.keypair f b disposedRun).1
      refine ⟨items,id,head,rfl,headId,by simp [TxDisposition.txPackets,device,stored],finished,unique,?_,?_⟩
      · simpa only [Erased,keptCells,dropCells] using erased
      · rw [queues,keptQueues,dropQueues]
        funext owner
        by_cases equal : owner=pid
        · subst owner
          simp only [ite_true]
          obtain ⟨d,p,device,found,_,_⟩:=txDrop_effect pid a e droppedRun
          have resident : peerAt w pid=some p:=by simp [peerAt,device,found]
          have selected:=cached p resident
          simp [txQueueContents,RxCredits.handoffTxView,peerAt,device,found,PrevQueue.all,PrevQueue.dropPeeked,selected]
        · simp only [equal,ite_false]

theorem ready_true (a b : Ambient)
    (run : ((txReadySource first).run w).run a=.ok ((true,v),b)) :
    ∃items id packet, first=some items ∧ items.head?=some id ∧
      TxDisposition.txPackets w id=some packet ∧ packet.state≠.uncrypted ∧ v=w := by
  cases first with
  | none => simp [txReadySource,WG.andM,branch,AmbientM.branch] at run
  | some items =>
    cases head : items.head? with
    | none =>
      simp [txReadySource,WG.andM,branch,AmbientM.branch,head,invariant,AmbientM.invariant] at run
      cases run
    | some id =>
      unfold txReadySource WG.andM at run
      rw [MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨present,t,e,presentRun,run⟩:=run
      cases presentRun
      simp only [Option.isSome_some,ite_true,head] at run
      rw [MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨packet,u,c,read,test⟩:=run
      obtain ⟨same,clock,d,device,stored⟩:=Packets.getTxSkb_current id w u packet _ c read
      subst u
      subst c
      have checked : (packet.state != .uncrypted)=true ∧ w=v ∧
          CounterWindow.record (CounterWindow.record a .txPacket true) .txNotUncrypted
            (packet.state != .uncrypted)=b := by
        simpa [branch,AmbientM.branch,CounterWindow.record,and_assoc] using test
      refine ⟨items,id,packet,rfl,head,?_,?_,checked.2.1.symm⟩
      · simp [TxDisposition.txPackets,device,stored]
      · intro equal
        rw [equal] at checked
        cases checked.1

theorem body_true (pid : PeerId) (a b : Ambient)
    (cached : ∀p,peerAt w pid=some p→p.txQueue.peeked=first)
    (run : ((TxDisposition.bodySource pid first).run w).run a=.ok ((true,v),b)) :
    ∃items id head, first=some items ∧ items.head?=some id ∧
      TxDisposition.txPackets w id=some head ∧ head.state≠.uncrypted ∧ items.Nodup ∧ Erased items w v ∧
      txQueueContents v=fun owner=>if owner=pid then (txQueueContents w pid).tail else txQueueContents w owner := by
  rw [tx_body_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ready,u,c,test,tail⟩:=run
  cases ready with
  | false => simp only [Bool.not_false,ite_true] at tail; cases tail
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    obtain ⟨items,id,packet,chosen,head,stored,marked,same⟩:=ready_true a c test
    subst u
    obtain ⟨other,otherId,otherPacket,chosen',head',stored',_,unique,erased,queues⟩:=ready_tail pid c b cached tail
    have itemsEqual : other=items:=Option.some.inj (chosen'.symm.trans chosen)
    subst other
    exact ⟨items,id,packet,chosen,head,stored,marked,unique,erased,queues⟩

/-- No incoming physical, lifetime or queue invariant is needed for the
normal source disposition. Those separate initialized facts identify these
unique owning occurrences with their prior admission and allocation. -/
theorem step (pid : PeerId) (a b : Ambient)
    (run : ((txStep pid).run w).run a=.ok ((result,v),b)) :
    (result=false ∧ TxDisposition.txPackets v=TxDisposition.txPackets w ∧
      txQueueContents v=txQueueContents w) ∨
    ∃p items id head, peerAt w pid=some p ∧ p.txQueue.all.head?=some items ∧
      items.head?=some id ∧ TxDisposition.txPackets w id=some head ∧ head.state≠.uncrypted ∧
      result=true ∧ items.Nodup ∧ Erased items w v ∧
      txQueueContents v=fun owner=>if owner=pid then (txQueueContents w pid).tail else txQueueContents w owner := by
  rw [txStep_peek_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨first,u,c,peek,body⟩:=run
  obtain ⟨d,p,queue,device,found,contents,cached,after⟩:=txPeek_effect pid a c peek
  have cells : TxDisposition.txPackets u=TxDisposition.txPackets w := by
    funext id
    simp [TxDisposition.txPackets,after,replacePeer,device]
  have queues : txQueueContents u=txQueueContents w := by
    funext owner
    by_cases same : owner=pid
    · subst owner
      simp [txQueueContents,RxCredits.handoffTxView,after,replacePeer,device,found,contents]
    · simp [txQueueContents,RxCredits.handoffTxView,after,replacePeer,device,
        Ne.symm same,Std.TreeMap.getElem?_insert]
  cases result with
  | false =>
    have same:=body_false_world pid first c b body
    exact Or.inl ⟨rfl,same ▸ cells,same ▸ queues⟩
  | true =>
    obtain ⟨items,id,head,selected,firstId,stored,marked,unique,erased,queueFinal⟩:=body_true pid c b (by
      intro q resident
      have same : q={p with txQueue:=queue}:=by simpa [peerAt,after,replacePeer] using resident.symm
      subst q
      exact cached) body
    refine Or.inr ⟨p,items,id,head,by simp [peerAt,device,found],?_,firstId,
      cells ▸ stored,marked,rfl,unique,?_,?_⟩
    · rw [←contents]
      simp [PrevQueue.all,cached,selected]
    · simpa only [Erased,cells] using erased
    · simpa only [queues] using queueFinal

end Leanux.Proofs.WG.RetirementSecurity.TxDispositionCoverage
