import Leanux.Proofs.WG.RetirementSecurity.TxWorkCompletionFrames
import Leanux.Proofs.WG.RetirementSecurity.TxWorkStep
import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceWorker

/-! Source TX iterations retain the reverse work obligations while their
actual peer actor is active. A normal false iteration discharges that actor
because its remaining queue has no terminal head. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem queue_contents (found : peerAt w pid=some p) : txQueueContents w pid=p.txQueue.all := by
  change ((peerAt w pid).map (·.txQueue.all)).getD []=p.txQueue.all
  rw [found]
  rfl

theorem queue_member (member : batch∈txQueueContents w pid) :
    ∃p,peerAt w pid=some p ∧ batch∈p.txQueue.all := by
  change batch∈((peerAt w pid).map (·.txQueue.all)).getD [] at member
  cases found:peerAt w pid with
  | none=>simp [found] at member
  | some p=>exact ⟨p,rfl,by simpa [found] using member⟩

theorem Obligations.contents (before : Obligations crypt tx w)
    (queues : txQueueContents v=txQueueContents w)
    (packets : TxDisposition.txPackets v=TxDisposition.txPackets w)
    (ring : txCryptItems v=txCryptItems w) (work : queued v=queued w) :
    Obligations crypt tx v := by
  constructor
  · intro pid p found batch member
    obtain ⟨q,stored,prior⟩:=queue_member (queues ▸ (queue_contents found).symm ▸ member)
    obtain ⟨first,packet,head,resident,pending⟩:=before.batches pid q stored batch prior
    exact ⟨first,packet,head,packets.symm ▸ resident,by simpa only [ring] using pending⟩
  · intro pid p found batch first packet headQueue head resident terminal
    have selected:(txQueueContents w pid).head?=some batch := by
      rw [←queues,queue_contents found]
      exact headQueue
    obtain ⟨q,stored,_⟩:=queue_member (List.mem_of_head? selected)
    have headOld:q.txQueue.all.head?=some batch := by simpa only [queue_contents stored] using selected
    simpa only [work] using before.heads pid q stored batch first packet headOld head
      (packets ▸ resident) terminal

theorem Obligations.step (before : Obligations crypt tx w)
    (inventory : TxInventory locals w) (active : pid∈tx) (a b : Ambient)
    (run : ((txStep pid).run w).run a=.ok ((result,v),b)) : Obligations crypt tx v := by
  have work:queued v=queued w := (ProjectedAction.iff_run_ambient _ _ _).mp
    (step_work pid) w a result v b run
  have ring:txCryptItems v=txCryptItems w := by
    have same:TxRing.nativeCell v=TxRing.nativeCell w :=
      (ProjectedAction.iff_run_ambient _ _ _).mp (TxDispositionCoverage.step_ring pid)
        w a result v b run
    simpa only [txCryptItems,TxRing.nativeCell,Option.map_map,Function.comp_def] using
      congrArg (fun cell : Option (Nat × PtrRing (List SkbId))=>
        (cell.map fun pair=>pair.2.items).getD []) same
  have after:=inventory.step pid a b run
  rcases TxDispositionCoverage.step pid a b run with ⟨_,cells,queues⟩ |
    ⟨owner,items,id,head,_,_,_,_,_,_,_,erased,queues⟩
  · exact before.contents queues cells ring work
  · have survivors (id : SkbId) (packet : DataPacket)
        (resident : TxDisposition.txPackets v id=some packet) :
        TxDisposition.txPackets w id=some packet := by
      rw [erased] at resident
      dsimp only at resident
      split at resident
      · cases resident
      · exact resident
    have subset (q : PeerId) : txQueueContents v q ⊆ txQueueContents w q := by
      rw [queues]
      dsimp only
      split
      · rename_i same
        subst q
        intro batch member
        exact List.mem_of_mem_tail member
      · exact List.Subset.refl _
    constructor
    · intro q p found batch member
      have atEnd:batch∈txQueueContents v q := (queue_contents found).symm ▸ member
      obtain ⟨old,stored,previous⟩:=queue_member (subset q atEnd)
      obtain ⟨first,packet,chosen,resident,pending⟩:=before.batches q old stored batch previous
      obtain ⟨finalPacket,finalResident⟩:=after.queueResident q p found first
        (List.mem_flatten.mpr ⟨batch,member,List.mem_of_head? chosen⟩)
      have equal:finalPacket=packet := Option.some.inj ((survivors first finalPacket finalResident).symm.trans resident)
      subst finalPacket
      exact ⟨first,packet,chosen,finalResident,by simpa only [ring] using pending⟩
    · intro q p found batch first packet selected chosen resident terminal
      by_cases same:q=pid
      · subst q
        exact List.mem_append_right _ active
      · have unchanged:txQueueContents v q=txQueueContents w q := by simp only [queues,ite_eq_right same]
        have oldHead:(txQueueContents w q).head?=some batch := by
          rw [←unchanged,queue_contents found]
          exact selected
        obtain ⟨old,stored,_⟩:=queue_member (List.mem_of_head? oldHead)
        have selectedOld:old.txQueue.all.head?=some batch := by
          simpa only [queue_contents stored] using oldHead
        simpa only [work] using before.heads q old stored batch first packet selectedOld
          chosen (survivors first packet resident) terminal

/-- Ending the actual peer actor does not abandon a terminal queue head.
The native false step itself supplies the empty/uncrypted alternative. -/
theorem Obligations.end_actor (before : Obligations crypt (pid::tx) w)
    (inventory : TxInventory locals w) (a b : Ambient)
    (run : ((txStep pid).run w).run a=.ok ((false,v),b)) : Obligations crypt tx v := by
  have held:=before.step inventory (by simp) a b run
  refine ⟨held.batches,?_⟩
  intro q p found batch first packet selected chosen resident terminal
  have pending:=held.heads q p found batch first packet selected chosen resident terminal
  rcases List.mem_append.mp pending with queued | active
  · exact List.mem_append_left _ queued
  · rcases List.mem_cons.mp active with same | remaining
    · subst q
      rcases ended_head pid a b run with empty | ⟨items,id,head,oldHead,headId,stored,uncrypted⟩
      · rw [←queue_contents found,empty] at selected
        cases selected
      · have selectedNow:(txQueueContents v pid).head?=some batch := by
          simpa only [queue_contents found] using selected
        have itemsEqual:items=batch := Option.some.inj (oldHead.symm.trans selectedNow)
        subst items
        have idEqual:id=first := Option.some.inj (headId.symm.trans chosen)
        subst id
        have packetEqual:head=packet := Option.some.inj (stored.symm.trans resident)
        exact (terminal (packetEqual ▸ uncrypted)).elim
    · exact List.mem_append_right _ remaining

end Leanux.Proofs.WG.RetirementSecurity.TxWork
