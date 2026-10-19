import Leanux.Proofs.WG.RetirementSecurity.TxDispositionCoverage
import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceAllocation

/-! The missing converse of physical TX inventory: every resident packet has
an owning peer queue or an explicit caller local. Device-ring entries are
aliases and add no owners. This state carrier is not by itself historical
conservation: socket/disposal outcomes and stopped local continuations remain
separate obligations. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
variable {id : SkbId}

def TxOwned (locals : List TxLocalBatch) (w : WGWorld) (id : SkbId) : Prop :=
  id∈txLocalItems locals ∨ ∃pid,id∈(txQueueContents w pid).flatten

def TxCoverage (locals : List TxLocalBatch) (w : WGWorld) : Prop :=
  ∀id packet,TxDisposition.txPackets w id=some packet→TxOwned locals w id

theorem initial_tx_coverage (net bare : Bool) : TxCoverage [] (Runner.initialWG net bare) := by
  intro id packet resident
  cases net <;> cases bare <;> simp [TxDisposition.txPackets,Runner.initialWG] at resident

theorem TxCoverage.transport (before : TxCoverage locals w)
    (packets : ∀id packet,TxDisposition.txPackets v id=some packet→
      ∃old,TxDisposition.txPackets w id=some old)
    (owners : ∀id,TxOwned locals w id→TxOwned next v id) : TxCoverage next v := by
  intro id packet resident
  obtain ⟨old,stored⟩:=packets id packet resident
  exact owners id (before id old stored)

theorem TxCoverage.frame (before : TxCoverage locals w)
    (presence : txPresent v=txPresent w) (queues : txQueueContents v=txQueueContents w) :
    TxCoverage locals v := by
  apply before.transport
  · intro id packet resident
    have present := congrFun presence id
    simp only [txPresent,resident,Option.isSome_some] at present
    exact Option.isSome_iff_exists.mp present.symm
  · intro id owned
    simpa only [TxOwned,queues] using owned

theorem TxCoverage.cells (before : TxCoverage locals w)
    (packets : TxDisposition.txPackets v=TxDisposition.txPackets w)
    (queues : txQueueContents v=txQueueContents w) : TxCoverage locals v :=
  before.frame (congrArg (fun cells id=>(cells id).isSome) packets) queues

/-- Complete native allocation introduces no packet cell outside its returned
IDs. This direction needs no freshness premise. -/
theorem allocate_survivor (packets : List DataPacket) (a b : Ambient)
    (run : ((packets.mapM newTxSkb).run w).run a=.ok ((items,v),b))
    (resident : TxDisposition.txPackets v id=some packet) :
    id∈items ∨ TxDisposition.txPackets w id=some packet := by
  induction packets generalizing w a items with
  | nil => simp only [List.mapM_nil] at run; cases run; exact Or.inr resident
  | cons first rest ih =>
    simp only [List.mapM_cons,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨head,u,c,allocated,tail,t,e,remaining,done⟩:=run
    cases done
    cases device : w.dev with
    | none => simp [newTxSkb,liftSkb_run,device] at allocated
    | some d =>
      rw [Packets.newTxSkb_run w a d first device] at allocated
      cases allocated
      rcases ih a remaining with member | old
      · exact Or.inl (List.mem_cons_of_mem _ member)
      · by_cases same : id=d.nextSkb
        · exact Or.inl (List.mem_cons.mpr (Or.inl same))
        · exact Or.inr (by simpa [TxDisposition.txPackets,Packets.update,device,
            Std.TreeMap.getElem?_insert,Ne.symm same] using old)

theorem TxCoverage.allocate (before : TxCoverage locals w) (pid : PeerId)
    (packets : List DataPacket) (a b : Ambient)
    (run : ((packets.mapM newTxSkb).run w).run a=.ok ((items,v),b)) :
    TxCoverage (⟨.unpublished,pid,items⟩::locals) v := by
  have perimeter := (ProjectedAction.iff_run_ambient _ _ _).mp
    (allocate_perimeter packets) w a items v b run
  have peers : peersAt v=peersAt w := congrArg (fun fields=>fields.2.1) perimeter
  have queues : txQueueContents v=txQueueContents w := by
    funext owner
    simpa only [txQueueContents,RxCredits.handoffTxView,peersAt,Option.bind_map,
      Option.map_bind,Function.comp_def] using
      congrArg (fun cells=>(cells.bind fun table=>table[owner]?.map (·.txQueue.all)).getD []) peers
  intro id packet resident
  rcases allocate_survivor packets a b run resident with fresh | old
  · exact Or.inl (by simp [txLocalItems,fresh])
  · rcases before id packet old with heldLocal | queued
    · exact Or.inl (List.mem_append.mpr (Or.inr heldLocal))
    · exact Or.inr (by simpa only [queues] using queued)

theorem TxCoverage.free_batch
    (before : TxCoverage (held::locals) w) (a b : Ambient)
    (run : ((TxDisposition.freeList held.items).run w).run a=.ok (((),v),b)) :
    TxCoverage locals v := by
  have packets := (hoare_iff_run_ambient _ _ _).mp
    (TxDisposition.freeList_wp held.items (TxDisposition.txPackets w)) w a () v b rfl run
  have peers := (ProjectedAction.iff_run_ambient _ _ _).mp (free_list_peer_frame held.items) w a () v b run
  have queues : txQueueContents v=txQueueContents w := by
    funext owner
    simpa only [txQueueContents,RxCredits.handoffTxView,peersAt,Option.bind_map,
      Option.map_bind,Function.comp_def] using
      congrArg (fun cells=>(cells.bind fun table=>table[owner]?.map (·.txQueue.all)).getD []) peers
  intro id packet resident
  have outside : id∉held.items := by intro inside; simp [packets,inside] at resident
  have old : TxDisposition.txPackets w id=some packet := by simpa [packets,outside] using resident
  rcases before id packet old with heldLocal | queued
  · exact Or.inl (by simpa [txLocalItems,outside] using heldLocal)
  · exact Or.inr (by simpa only [queues] using queued)

theorem TxCoverage.step (before : TxCoverage locals w) (pid : PeerId) (a b : Ambient)
    (run : ((txStep pid).run w).run a=.ok ((result,v),b)) : TxCoverage locals v := by
  rcases TxDispositionCoverage.step pid a b run with ⟨_,packets,queues⟩ |
    ⟨p,items,headId,head,peer,first,_,_,_,_,_,erased,queues⟩
  · exact before.cells packets queues
  · change TxDisposition.txPackets v=(fun id=>if id∈items then none else TxDisposition.txPackets w id) at erased
    intro id packet resident
    have outside : id∉items := by intro inside; simp [erased,inside] at resident
    have old : TxDisposition.txPackets w id=some packet := by
      simpa [TxDispositionCoverage.Erased,erased,outside] using resident
    rcases before id packet old with heldLocal | ⟨owner,queued⟩
    · exact Or.inl heldLocal
    · refine Or.inr ⟨owner,?_⟩
      rw [queues]
      by_cases same : owner=pid
      · subst owner
        simp only [ite_true]
        have queue : txQueueContents w pid=p.txQueue.all := by
          change ((peerAt w pid).map (·.txQueue.all)).getD []=p.txQueue.all
          simp [peer]
        rw [queue] at queued ⊢
        have split : p.txQueue.all=items::p.txQueue.all.tail := by
          cases queueEq : p.txQueue.all with
          | nil => simp [queueEq] at first
          | cons x xs => simp [queueEq] at first; simp [first]
        rw [split,List.flatten_cons,List.mem_append] at queued
        exact queued.resolve_left outside
      · simpa [same] using queued

theorem TxCoverage.points (before : TxCoverage locals w)
    (same : ownershipPointView v=ownershipPointView w) : TxCoverage locals v := by
  apply before.frame
  · funext id
    have point := congrFun (congrArg (fun fields=>fields.2.2.2.1) same) id
    change (TxDisposition.txPackets v id).map (·.keypair)=
      (TxDisposition.txPackets w id).map (·.keypair) at point
    simpa only [txPresent,Option.isSome_map] using congrArg Option.isSome point
  · funext pid
    have point := congrFun (congrArg (fun fields=>fields.2.2.1) same) pid
    change (peerAt v pid).map peerOwnership=(peerAt w pid).map peerOwnership at point
    simpa only [txQueueContents,RxCredits.handoffTxView,peerAt,peerOwnership,
      Option.map_map,Option.map_bind,Function.comp_def] using
      congrArg (fun value=>(value.map fun fields=>fields.2.1).getD []) point

theorem TxCoverage.exchange (before : TxCoverage locals w)
    (device : w.dev=some d) (found : d.peers[pid]?=some p) (q : Peer)
    (transfer : (txLocalItems locals++txPeerItems p).Perm
      (txLocalItems next++txPeerItems q)) : TxCoverage next (replacePeer w d pid q) := by
  have packets : TxDisposition.txPackets (replacePeer w d pid q)=TxDisposition.txPackets w := by
    funext id; simp [TxDisposition.txPackets,replacePeer,device]
  have move (id : SkbId) (member : id∈txLocalItems locals++txPeerItems p) :
      TxOwned next (replacePeer w d pid q) id := by
    rcases List.mem_append.mp (transfer.mem_iff.mp member) with held | queued
    · exact Or.inl held
    · exact Or.inr ⟨pid,by simpa [txQueueContents,RxCredits.handoffTxView,replacePeer,txPeerItems] using queued⟩
  intro id packet resident
  rcases before id packet (by simpa only [packets] using resident) with held | ⟨owner,queued⟩
  · exact move id (List.mem_append_left _ held)
  · by_cases same : owner=pid
    · subst owner
      exact move id (List.mem_append_right _ (by
        simpa [txQueueContents,RxCredits.handoffTxView,device,found,txPeerItems] using queued))
    · exact Or.inr ⟨owner,by
        simpa [txQueueContents,RxCredits.handoffTxView,replacePeer,device,
          Std.TreeMap.getElem?_insert,Ne.symm same] using queued⟩

theorem TxCoverage.enqueue (before : TxCoverage (⟨.unpublished,pid,items⟩::locals) w)
    (device : w.dev=some d) (found : d.peers[pid]?=some p) :
    TxCoverage locals (replacePeer w d pid {p with txQueue:=p.txQueue.enqueue items}) := by
  apply before.exchange device found
  apply List.perm_iff_count.mpr
  intro id
  simp [txLocalItems,txPeerItems,Queues.prev_enqueue_all,List.flatten_append,List.count_append]
  omega

theorem TxCoverage.drop (before : TxCoverage locals w)
    (device : w.dev=some d) (found : d.peers[pid]?=some p)
    (peeked : p.txQueue.peeked=some items) :
    TxCoverage (⟨.selected,pid,items⟩::locals)
      (replacePeer w d pid {p with txQueue:=p.txQueue.dropPeeked}) := by
  apply before.exchange device found
  apply List.perm_iff_count.mpr
  intro id
  simp [txLocalItems,txPeerItems,PrevQueue.all,PrevQueue.dropPeeked,peeked,List.count_append]
  omega

end Leanux.Proofs.WG.RetirementSecurity
