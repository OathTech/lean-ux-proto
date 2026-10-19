import Leanux.Proofs.WG.RetirementSecurity.TxWorkPoll
import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextCompletion

/-! Encryption byte writes preserve queue-head service state. The projection
keeps packet residency and marks, while omitting bytes that the native loop
is explicitly allowed to replace. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

def marks (w : WGWorld) (id : SkbId) := (TxDisposition.txPackets w id).map (·.state)

theorem Obligations.mark_frames (before : Obligations crypt tx w)
    (queues : txQueueContents v=txQueueContents w) (states : marks v=marks w)
    (ring : txCryptItems v=txCryptItems w) (work : queued v=queued w) :
    Obligations crypt tx v := by
  constructor
  · intro pid p found batch member
    obtain ⟨q,stored,prior⟩:=queue_member (queues ▸ (queue_contents found).symm ▸ member)
    obtain ⟨first,packet,head,resident,pending⟩:=before.batches pid q stored batch prior
    have same:=congrFun states first
    simp only [marks,resident,Option.map_some] at same
    obtain ⟨current,cell,state⟩:=Option.map_eq_some_iff.mp same
    exact ⟨first,current,head,cell,fun uncrypted=>by
      simpa only [ring] using pending (state.symm.trans uncrypted)⟩
  · intro pid p found batch first packet headQueue head resident terminal
    have selected:(txQueueContents w pid).head?=some batch := by
      rw [←queues,queue_contents found]
      exact headQueue
    obtain ⟨q,stored,_⟩:=queue_member (List.mem_of_head? selected)
    have headOld:q.txQueue.all.head?=some batch := by simpa only [queue_contents stored] using selected
    have same:=congrFun states first
    simp only [marks,resident,Option.map_some] at same
    obtain ⟨original,cell,state⟩:=Option.map_eq_some_iff.mp same.symm
    simpa only [work] using before.heads pid q stored batch first original headOld head cell
      (fun uncrypted=>terminal (state.symm.trans uncrypted))

theorem Obligations.store (before : Obligations crypt tx w) (same : wgStoreView v=wgStoreView w) :
    Obligations crypt tx v := by
  have device:v.dev=w.dev:=congrArg WGStoreView.dev same
  exact before.contents (by funext pid; simp only [txQueueContents,RxCredits.handoffTxView,device])
    (by funext id; simp only [TxDisposition.txPackets,device])
    (by simp only [txCryptItems,device]) (by simp only [queued,device])

theorem bytes_marks (id : SkbId) (bytes : List UInt8) :
    SameView marks (setTxSkb id (fun p=>{p with bytes})) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  cases device:w.dev with
  | none=>simp [setTxSkb,liftSkb_run,device] at run
  | some d=>
    cases stored:d.txSkbs[id]? with
    | none=>
      simp [setTxSkb,liftSkb_run,SkbStore.setTx,SkbStore.getTx,device,stored,invariant,AmbientM.invariant] at run
      cases run
    | some p=>
      rw [Packets.setTxSkb_run w a d id p (fun p=>{p with bytes}) device stored] at run
      cases run
      funext other
      by_cases same:id=other
      · subst other; simp [marks,TxDisposition.txPackets,Packets.update,device,stored]
      · simp [marks,TxDisposition.txPackets,Packets.update,device,Std.TreeMap.getElem?_insert,same]

theorem bytes_ring (id : SkbId) (bytes : List UInt8) :
    SameView TxRing.nativeCell (setTxSkb id (fun p=>{p with bytes})) := by
  intro initial
  apply hoare_liftSkb
  intro w d store before device
  simpa only [TxRing.nativeCell,device,Option.map_some] using before

theorem Obligations.write_bytes (before : Obligations crypt tx w)
    (id : SkbId) (bytes : List UInt8) (a b : Ambient)
    (run : ((setTxSkb id (fun p=>{p with bytes})).run w).run a=.ok (((),v),b)) :
    Obligations crypt tx v := by
  have points:=(ProjectedAction.iff_run_ambient _ _ _).mp
    (ownershipPoints_holderStore _ (setTx_holderStore id (fun p=>{p with bytes}) (fun _=>rfl)))
      w a () v b run
  have queues:=ownership_points_queues points
  exact before.mark_frames (by funext pid; exact congrArg (fun queues=>(queues pid).getD []) queues)
    ((ProjectedAction.iff_run_ambient _ _ _).mp (bytes_marks id bytes) w a () v b run)
    (crypt_items_eq ((ProjectedAction.iff_run_ambient _ _ _).mp (bytes_ring id bytes) w a () v b run))
    ((ProjectedAction.iff_run_ambient _ _ _).mp (set_packet_work id _) w a () v b run)

end Leanux.Proofs.WG.RetirementSecurity.TxWork
