import Leanux.Proofs.WG.RetirementSecurity.TxWorkAllocation

/-! A real encrypt-ring poll transfers its service obligation to the
selected continuation, retaining the owning peer queue and pending TX actors. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem Obligations.transfer (before : Obligations crypt tx w)
    (queues : txQueueContents v=txQueueContents w)
    (cells : TxDisposition.txPackets v=TxDisposition.txPackets w)
    (service : ∀batch,batch∈txCryptItems w++crypt→batch∈txCryptItems v++nextCrypt)
    (actors : ∀pid,pid∈queued w++tx→pid∈queued v++nextTx) :
    Obligations nextCrypt nextTx v := by
  constructor
  · intro pid p found batch member
    obtain ⟨q,stored,prior⟩:=queue_member (queues ▸ (queue_contents found).symm ▸ member)
    obtain ⟨first,packet,head,resident,pending⟩:=before.batches pid q stored batch prior
    exact ⟨first,packet,head,cells.symm ▸ resident,fun uncrypted=>service batch (pending uncrypted)⟩
  · intro pid p found batch first packet headQueue head resident terminal
    have selected:(txQueueContents w pid).head?=some batch := by
      rw [←queues,queue_contents found]
      exact headQueue
    obtain ⟨q,stored,_⟩:=queue_member (List.mem_of_head? selected)
    have headOld:q.txQueue.all.head?=some batch := by simpa only [queue_contents stored] using selected
    exact actors pid (before.heads pid q stored batch first packet headOld head (cells ▸ resident) terminal)

theorem poll_work : SameView queued TxRing.pollSource := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold TxRing.pollSource
  repeat' tx_work_step initial

theorem poll_cells : SameView TxDisposition.txPackets TxRing.pollSource := by
  intro initial
  change Preserves (fun w=>TxDisposition.txPackets w=initial) _
  unfold TxRing.pollSource
  repeat' first
    | (rx_retention_head getDev; exact (TxDisposition.packets_kernel getDev_sameWGStore).wp (·=initial))
    | (rx_retention_head modifyDev
       apply hoare_modify
       intro w before
       rw [←before]
       funext id
       simp only [TxDisposition.txPackets,Option.bind_map,Function.comp_def])
    | rx_retention_step

theorem Obligations.poll (before : Obligations crypt tx w)
    (physical : TxDisposition.LiveFrontier.Physical w) (a b : Ambient)
    (run : (TxRing.pollSource.run w).run a=.ok ((out,v),b)) :
    Obligations (out.toList++crypt) tx v := by
  cases device:w.dev with
  | none=>simp [TxRing.pollSource,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d=>
    obtain ⟨n,h,refines⟩:=physical d device
    have cell:TxRing.nativeCell w=some (d.ifindex,d.encryptQueue) := by simp [TxRing.nativeCell,device]
    obtain ⟨selected,installed⟩:=TxRing.poll_result cell run
    have old:=refines.initialized.2.1
    have after:=(refines.step .poll).initialized.2.1
    simp only [Ring.Journal.step,Ring.Journal.admitted,Ring.Journal.consumed,
      List.filterMap_append,List.filterMap_cons,List.filterMap_nil,List.append_nil] at after
    change Ring.Journal.admitted h=(Ring.Journal.consumed h++d.encryptQueue.consume.1.toList)++
      d.encryptQueue.consume.2.items at after
    rw [old,List.append_assoc] at after
    have sequence:d.encryptQueue.items=out.toList++d.encryptQueue.consume.2.items := by
      simpa only [selected] using List.append_cancel_left after
    have live:txCryptItems v=d.encryptQueue.consume.2.items := by
      simpa only [TxRing.nativeCell,txCryptItems,Option.map_map,Function.comp_def,Option.map_some,Option.getD_some] using
        congrArg (fun cell=>(cell.map fun pair=>pair.2.items).getD []) installed
    have queues:txQueueContents v=txQueueContents w := by
      have fields:=ownership_points_queues ((ProjectedAction.iff_run_ambient _ _ _).mp
        OccurrenceEncrypt.poll_points w a out v b run)
      funext pid
      exact congrArg (fun queues=>(queues pid).getD []) fields
    have work:=(ProjectedAction.iff_run_ambient _ _ _).mp poll_work w a out v b run
    apply before.transfer queues ((ProjectedAction.iff_run_ambient _ _ _).mp poll_cells w a out v b run)
      ?_ (fun _ pending=>by simpa only [work] using pending)
    intro batch pending
    have oldRing:txCryptItems w=out.toList++d.encryptQueue.consume.2.items := by
      simpa only [txCryptItems,device,Option.map_some,Option.getD_some] using sequence
    rw [oldRing] at pending
    rw [live]
    simp only [List.mem_append] at pending ⊢
    rcases pending with (selected | remaining) | active
    · exact .inr (.inl selected)
    · exact .inl remaining
    · exact .inr (.inr active)

end Leanux.Proofs.WG.RetirementSecurity.TxWork
