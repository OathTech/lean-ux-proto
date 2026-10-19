import Leanux.Proofs.WG.RetirementSecurity.TxWorkTransfers

/-! Native admission establishes the reverse encryption-service obligation.
EPIPE keeps an explicit in-flight publication continuation until the actual
DEAD publication; successful ring insertion stores the service alias in the
physical ring. A peer-queue refusal adds neither owning queue nor service. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

def publicationPending (ret : Int) (items : List SkbId) (crypt : List (List SkbId)) :=
  if ret = -Leanux.EPIPE then items::crypt else crypt

theorem set_packet_work (id : SkbId) (f : DataPacket→DataPacket) : SameView queued (setTxSkb id f) := by
  intro initial
  apply hoare_liftSkb
  intro w d packets before device
  simpa only [queued,device,Option.map_some,Option.getD_some] using before

theorem admission_work (pid : PeerId) (items : List SkbId) :
    SameView queued (enqueuePerDeviceAndPeer pid items) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold enqueuePerDeviceAndPeer cpumaskNextOnlineFrom
  simp only [branch,queueDeviceWork,invariant]
  repeat' first
    | (rx_retention_head setTxSkb; exact (set_packet_work _ _).wp (·=initial))
    | tx_work_step initial

theorem Obligations.admission (before : Obligations crypt tx w)
    (inventory : TxInventory (⟨.unpublished,pid,items⟩::locals) w)
    (physical : TxDisposition.LiveFrontier.Physical w) (device : w.dev=some d)
    (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid items).run w).run a=.ok ((ret,v),b)) :
    Obligations (publicationPending ret items crypt) tx v := by
  have ring:=admission_ring physical device pid items a b run
  have work:queued v=queued w := (ProjectedAction.iff_run_ambient _ _ _).mp
    (admission_work pid items) w a ret v b run
  have carry (batch : List SkbId) (pending : batch∈txCryptItems w++crypt) :
      batch∈txCryptItems v++publicationPending ret items crypt := by
    rw [ring]
    unfold publicationPending
    split <;> split
    all_goals simp only [List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,or_assoc]
    all_goals rcases List.mem_append.mp pending with member | member
    all_goals first
      | exact Or.inl member
      | exact Or.inr member
      | exact Or.inr (Or.inr member)
      | exact Or.inr (Or.inr (Or.inr member))
  have oldHead (q : PeerId) (p : Peer) (found : peerAt w q=some p)
      (batch : List SkbId) (member : batch∈p.txQueue.all) :
      ∃first packet,batch.head?=some first ∧ TxDisposition.txPackets v first=some packet ∧
        TxDisposition.txPackets w first=some packet ∧
        (packet.state=.uncrypted→batch∈txCryptItems v++publicationPending ret items crypt) := by
    obtain ⟨first,packet,head,resident,pending⟩:=before.batches q p found batch member
    have outside:first∉items := by
      intro inside
      exact inventory.localsSeparate q p found first (by simp [txLocalItems,inside])
        (List.mem_flatten.mpr ⟨batch,member,List.mem_of_head? head⟩)
    have same:TxDisposition.txPackets v first=TxDisposition.txPackets w first :=
      (ProjectedAction.iff_run_ambient _ _ _).mp
        (TxDisposition.MarkTransport.enqueue_other first pid items outside) w a ret v b run
    exact ⟨first,packet,head,same.trans resident,resident,fun state=>carry batch (pending state)⟩
  have shape (q : PeerId) (p : Peer) (found : peerAt v q=some p) :
      ∃old,peerAt w q=some old ∧ p.txQueue.all=old.txQueue.all++
        (if (ret=0 ∨ ret = -Leanux.EPIPE) ∧ q=pid then [items] else []) := by
    have output:RxCredits.handoffTxView v q=some p.txQueue.all := by
      change (peerAt v q).map (·.txQueue.all)=some p.txQueue.all
      rw [found]; rfl
    rcases enqueue_queue_effect pid items a b run with ⟨refused,queues⟩ | ⟨accepted,_,queues⟩
    · rw [queues] at output
      obtain ⟨old,stored,equal⟩:=Option.map_eq_some_iff.mp output
      refine ⟨old,stored,?_⟩
      have rejected:¬(ret=0 ∨ ret = -Leanux.EPIPE) := by
        rw [refused]
        decide
      simpa only [rejected,false_and,ite_false,List.append_nil] using equal.symm
    · have after:=queues q
      rw [output] at after
      obtain ⟨batches,original,equal⟩:=Option.map_eq_some_iff.mp after.symm
      obtain ⟨old,stored,contents⟩:=Option.map_eq_some_iff.mp original
      refine ⟨old,stored,?_⟩
      simpa only [accepted,true_and,contents] using equal.symm
  have fresh : ∃first packet,items.head?=some first ∧ TxDisposition.txPackets v first=some packet ∧
      packet.state=.uncrypted := by
    cases head:items.head? with
    | none=>simp only [enqueuePerDeviceAndPeer,head] at run; cases run
    | some first=>
      obtain ⟨packet,resident⟩:=inventory.localResident first
        (by simp [txLocalItems,List.mem_of_head? head])
      obtain ⟨result,stored,state⟩:=enqueue_head_uncrypted head resident pid a b run
      exact ⟨first,result,rfl,stored,state⟩
  have freshPending (accepted : ret=0 ∨ ret = -Leanux.EPIPE) :
      items∈txCryptItems v++publicationPending ret items crypt := by
    rcases accepted with success | pipe
    · simp [ring,success]
    · simp [publicationPending,pipe]
  constructor
  · intro q p found batch member
    obtain ⟨old,stored,contents⟩:=shape q p found
    rw [contents] at member
    rcases List.mem_append.mp member with previous | freshMember
    · obtain ⟨first,packet,head,resident,_,pending⟩:=oldHead q old stored batch previous
      exact ⟨first,packet,head,resident,pending⟩
    · split at freshMember
      · rename_i admitted
        have same:batch=items := by simpa only [List.mem_singleton] using freshMember
        subst batch
        obtain ⟨first,packet,head,resident,state⟩:=fresh
        exact ⟨first,packet,head,resident,fun _=>freshPending admitted.1⟩
      · simp at freshMember
  · intro q p found batch first packet selected chosen resident terminal
    obtain ⟨old,stored,contents⟩:=shape q p found
    cases queue:old.txQueue.all with
    | nil=>
      rw [contents,queue,List.nil_append] at selected
      split at selected
      · have same:items=batch := by simpa only [List.head?_cons,Option.some.injEq] using selected
        subst batch
        obtain ⟨id,head,headId,storedHead,uncrypted⟩:=fresh
        have sameId:id=first := Option.some.inj (headId.symm.trans chosen)
        subst id
        have samePacket:head=packet := Option.some.inj (storedHead.symm.trans resident)
        exact (terminal (samePacket ▸ uncrypted)).elim
      · cases selected
    | cons oldBatch rest=>
      have same:oldBatch=batch := by simpa only [contents,queue,List.cons_append,List.head?_cons,Option.some.injEq] using selected
      subst oldBatch
      obtain ⟨id,head,headId,storedHead,previous,_⟩:=oldHead q old stored batch (by simp [queue])
      have sameId:id=first := Option.some.inj (headId.symm.trans chosen)
      subst id
      have samePacket:head=packet := Option.some.inj (storedHead.symm.trans resident)
      subst head
      simpa only [work] using before.heads q old stored batch first packet
        (by simp [queue]) chosen previous terminal

end Leanux.Proofs.WG.RetirementSecurity.TxWork
