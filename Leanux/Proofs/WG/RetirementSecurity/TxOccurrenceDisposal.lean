import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceEnqueue

/-! Original disposal removes one selected batch from the physical
inventory. The remaining packets survive list free and key/peer payment;
normal final peer deletion retains every other queue. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem TxInventory.without_first (inventory : TxInventory (held :: locals) w) :
    TxInventory locals w := by
  refine ⟨(List.nodup_append.mp inventory.localUnique).2.1,
    inventory.queueUnique,inventory.peersSeparate,?_,?_,inventory.queueResident⟩
  · intro pid p found id member
    exact inventory.localsSeparate pid p found id (List.mem_append_right held.items member)
  · intro id member
    exact inventory.localResident id (List.mem_append_right held.items member)

theorem TxInventory.free_batch (inventory : TxInventory (held :: locals) w)
    (a b : Ambient)
    (run : ((Queues.TxDisposition.freeList held.items).run w).run a = .ok (((),v),b)) :
    TxInventory locals v ∧ ∀ id ∈ held.items, Queues.TxDisposition.txPackets v id = none := by
  have peers := (ProjectedAction.iff_run_ambient _ _ _).mp (free_list_peer_frame held.items)
    w a () v b run
  have cells : ∀ pid, peerAt v pid = peerAt w pid := by
    intro pid
    simpa [peerAt,peersAt,Option.bind_map,Function.comp_def] using
      congrArg (fun entries => entries.bind fun peers => peers[pid]?) peers
  have effect := (hoare_iff_run_ambient _ _ _).mp
    (Queues.TxDisposition.freeList_wp held.items (Queues.TxDisposition.txPackets w)) w a () v b rfl run
  have kept (id : SkbId) (outside : id ∉ held.items) :
      Queues.TxDisposition.txPackets v id = Queues.TxDisposition.txPackets w id := by
    simpa [outside] using congrFun effect id
  have remaining := inventory.without_first
  refine ⟨⟨remaining.localUnique,?_,?_,?_,?_,?_⟩,?_⟩
  · intro pid p found
    exact remaining.queueUnique pid p ((cells pid).symm.trans found)
  · intro pid p other q found otherFound different
    exact remaining.peersSeparate pid p other q ((cells pid).symm.trans found)
      ((cells other).symm.trans otherFound) different
  · intro pid p found
    exact remaining.localsSeparate pid p ((cells pid).symm.trans found)
  · intro id member
    have outside : id ∉ held.items := by
      intro selected
      exact (List.nodup_append.mp inventory.localUnique).2.2 id selected id member rfl
    obtain ⟨packet,resident⟩ := remaining.localResident id member
    exact ⟨packet,(kept id outside).trans resident⟩
  · intro pid p found id member
    have oldFound := (cells pid).symm.trans found
    have outside : id ∉ held.items := by
      intro selected
      exact inventory.localsSeparate pid p oldFound id (by simp [txLocalItems,selected]) member
    obtain ⟨packet,resident⟩ := remaining.queueResident pid p oldFound id member
    exact ⟨packet,(kept id outside).trans resident⟩
  · intro id member
    simpa [member] using congrFun effect id

theorem TxInventory.payment_frame (inventory : TxInventory locals w)
    (frame : Queues.RxCredits.DurableHolders.Frame w v)
    (packets : Queues.TxDisposition.txPackets v = Queues.TxDisposition.txPackets w) :
    TxInventory locals v := by
  apply inventory.transport
  · intro pid p found
    have old := frame.tx pid p.txQueue.all (by
      simpa [Queues.RxCredits.handoffTxView,peerAt] using congrArg (Option.map (fun p => p.txQueue.all)) found)
    change (peerAt w pid).map (fun p => p.txQueue.all) = some p.txQueue.all at old
    obtain ⟨q,resident,queue⟩ := Option.map_eq_some_iff.mp old
    exact ⟨q,resident,congrArg List.flatten queue⟩
  · intro id packet resident
    exact ⟨packet,(congrFun packets id).trans resident⟩

theorem TxInventory.key_put (inventory : TxInventory locals w) (kp : Option KeypairId) (now : Bool)
    (a b : Ambient) (run : ((keypairPut kp now).run w).run a = .ok (((),v),b)) :
    TxInventory locals v := inventory.payment_frame
  ((hoare_iff_run_ambient _ _ _).mp (Queues.RxCredits.HolderWorkFrames.keypairPut_frame kp now w)
    w a () v b (Queues.RxCredits.DurableHolders.Frame.refl w) run)
  ((ProjectedAction.iff_run_ambient _ _ _).mp (Queues.TxDisposition.keyPut_packets kp now) w a () v b run)

theorem TxInventory.peer_put (inventory : TxInventory locals w) (pid : Option PeerId)
    (a b : Ambient) (run : ((peerPut pid).run w).run a = .ok (((),v),b)) :
    TxInventory locals v := inventory.payment_frame
  ((hoare_iff_run_ambient _ _ _).mp (Queues.RxCredits.HolderWorkFrames.peerPut_frame pid w)
    w a () v b (Queues.RxCredits.DurableHolders.Frame.refl w) run)
  ((ProjectedAction.iff_run_ambient _ _ _).mp (Queues.TxDisposition.peerPut_packets pid) w a () v b run)

theorem TxInventory.dispose (inventory : TxInventory (⟨.selected,pid,items⟩ :: locals) w)
    (kid : KeypairId) (a b : Ambient)
    (run : ((Queues.TxDisposition.disposeSource pid items kid).run w).run a = .ok ((result,v),b)) :
    result = true ∧ TxInventory locals v := by
  have factor : Queues.TxDisposition.disposeSource pid items kid = (do
      Queues.TxDisposition.freeList items
      keypairPut (some kid) false
      peerPut (some pid)
      pure true) := by simp [Queues.TxDisposition.disposeSource,Queues.TxDisposition.freeList]
  rw [factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,freeRun,_,t,e,keyRun,_,s,f,peerRun,done⟩ := run
  cases done
  exact ⟨rfl,((inventory.free_batch a c freeRun).1.key_put (some kid) false c e keyRun).peer_put
    (some pid) e b peerRun⟩

end Leanux.Proofs.WG.RetirementSecurity
