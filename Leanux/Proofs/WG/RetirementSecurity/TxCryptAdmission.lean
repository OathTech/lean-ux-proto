import Leanux.Proofs.WG.RetirementSecurity.TxCryptOccurrences

/-! Exact native admission attaches a physical batch to its authoritative
peer queue before its ring alias is offered. The refusal leaves peer queues
unchanged; ring refusal still installs the authoritative peer occurrence. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem ownership_points_queues (same : ownershipPointView v = ownershipPointView w) :
    handoffTxView v = handoffTxView w := by
  funext pid
  have point := congrFun (congrArg (fun view => view.2.2.1) same) pid
  have mapped := congrArg (Option.map (fun fields : PeerOwnership => fields.2.1)) point
  simpa only [handoffTxView,ownershipPointView,ownershipAt,peerOwnership,peerAt,
    Option.map_map,Function.comp_def] using mapped

def EnqueueQueueEffect (pid : PeerId) (items : List SkbId) (w v : WGWorld) (ret : Int) : Prop :=
  (ret = -Leanux.ENOSPC ∧ handoffTxView v = handoffTxView w) ∨
  ((ret = 0 ∨ ret = -Leanux.EPIPE) ∧
    (∃ p, peerAt w pid = some p) ∧
    ∀ q, handoffTxView v q = (handoffTxView w q).map
      (fun batches => batches ++ if q = pid then [items] else []))

theorem enqueue_queue_effect (pid : PeerId) (items : List SkbId) (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid items).run w).run a = .ok ((ret,v),b)) :
    EnqueueQueueEffect pid items w v ret := by
  rw [enqueue_factor] at run
  cases head : items.head? with
  | none => simp only [head] at run; cases run
  | some first =>
    simp only [head,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨_,u,c,markRun,p,t,e,peerRun,full,s,f,branchRun,tail⟩ := run
    have marked := (ProjectedAction.iff_run_ambient _ _ _).mp
      (ownershipPoints_holderStore _
        (setTx_holderStore first (fun p => {p with state := .uncrypted}) (fun _ => rfl)))
      w a () u c markRun
    have before := ownership_points_queues marked
    obtain ⟨same,_,d,device,found⟩ := Origins.getPeer_return pid u t p c e peerRun
    subst t
    have same : s = u := by cases branchRun; rfl
    subst s
    cases full with
    | true =>
      simp only [ite_true] at tail
      cases tail
      exact Or.inl ⟨rfl,before⟩
    | false =>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨_,s,g,installRun,tailRun⟩ := tail
      have installed : replacePeer u d pid {p with txQueue := p.txQueue.enqueue items} = s ∧ f = g := by
        simpa [setPeer,modifyDev,replacePeer,device] using installRun
      have after := ownership_points_queues ((ProjectedAction.iff_run_ambient _ _ _).mp
        (enqueue_tail_ownership items) s g ret v b tailRun)
      refine Or.inr ⟨enqueue_tail_result items g b tailRun,?_,?_⟩
      · have old : handoffTxView w pid = some p.txQueue.all := by
          rw [← before]
          simp [handoffTxView,device,found]
        obtain ⟨q,resident,_⟩ := Option.map_eq_some_iff.mp old
        exact ⟨q,resident⟩
      · intro q
        rw [after,← installed.1,← before]
        by_cases eq : q = pid
        · subst q
          simp [handoffTxView,replacePeer,device,found,prev_enqueue_all]
        · simp [handoffTxView,replacePeer,device,Std.TreeMap.getElem?_insert,eq,Ne.symm eq,Function.comp_def]

theorem EnqueueQueueEffect.keeps (effect : EnqueueQueueEffect pid items w v ret)
    (owned : TxQueuedBatch w batch) : TxQueuedBatch v batch := by
  obtain ⟨q,p,found,member⟩ := owned
  have original : handoffTxView w q = some p.txQueue.all := by
    simpa only [handoffTxView,peerAt,Option.map_some] using congrArg (Option.map (fun p => p.txQueue.all)) found
  rcases effect with ⟨_,same⟩ | ⟨_,_,after⟩
  · rw [← same] at original
    obtain ⟨r,resident,queue⟩ := Option.map_eq_some_iff.mp original
    exact ⟨q,r,resident,queue.symm ▸ member⟩
  · have appended := after q
    rw [original] at appended
    obtain ⟨r,resident,queue⟩ := Option.map_eq_some_iff.mp appended
    exact ⟨q,r,resident,queue.symm ▸ List.mem_append_left _ member⟩

theorem EnqueueQueueEffect.installed (effect : EnqueueQueueEffect pid items w v ret)
    (accepted : ret = 0 ∨ ret = -Leanux.EPIPE) : TxQueuedBatch v items := by
  rcases effect with ⟨refused,_⟩ | ⟨_,⟨p,found⟩,after⟩
  · rcases accepted with zero | pipe <;> simp_all [Leanux.ENOSPC,Leanux.EPIPE]
  · have original : handoffTxView w pid = some p.txQueue.all := by
      simpa only [handoffTxView,peerAt,Option.map_some] using congrArg (Option.map (fun p => p.txQueue.all)) found
    have appended := after pid
    rw [original] at appended
    simp only [ite_true,Option.map_some] at appended
    obtain ⟨q,resident,queue⟩ := Option.map_eq_some_iff.mp appended
    exact ⟨pid,q,resident,queue.symm ▸ (by simp)⟩

theorem enqueue_head_uncrypted (head : items.head? = some first)
    (resident : TxDisposition.txPackets w first = some packet) (pid : PeerId) (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid items).run w).run a = .ok ((ret,v),b)) :
    TxDisposition.HeadState first .uncrypted v := by
  rw [enqueue_factor] at run
  simp only [head,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨_,u,c,markRun,tail⟩ := run
  have marked : TxDisposition.HeadState first .uncrypted u := by
    cases device : w.dev with
    | none => simp [TxDisposition.txPackets,device] at resident
    | some d =>
      have found : d.txSkbs[first]? = some packet := by simpa [TxDisposition.txPackets,device] using resident
      rw [Packets.setTxSkb_run w a d first packet _ device found] at markRun
      cases markRun
      exact ⟨{packet with state := .uncrypted},by simp [TxDisposition.txPackets,Packets.update,device],rfl⟩
  have rest : Preserves (TxDisposition.HeadState first .uncrypted) (do
      let p ← getPeer pid
      if ← branch .enqueuePeerQueueFull (p.txQueue.count ≥ MAX_QUEUED_PACKETS) then return -Leanux.ENOSPC
      setPeer pid {p with txQueue := p.txQueue.enqueue items}
      enqueueTailItem items) := by
    have shape : SameView StagingOccurrences.geometry (do
        let p ← getPeer pid
        if ← branch .enqueuePeerQueueFull (p.txQueue.count ≥ MAX_QUEUED_PACKETS) then return -Leanux.ENOSPC
        setPeer pid {p with txQueue := p.txQueue.enqueue items}
        enqueueTailItem items) := by
      intro initial
      change Preserves (fun w => StagingOccurrences.geometry w = initial) _
      unfold enqueueTailItem cpumaskNextOnlineFrom
      simp only [branch,queueDeviceWork]
      repeat' first
        | (allocation_release_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
        | staging_geometry_step initial
    exact shape.wp (fun geometry => ∃ p, geometry.2 first = some p ∧ p.state = .uncrypted)
  exact (hoare_iff_run_ambient _ _ _).mp rest u c ret v b marked (by
    simpa only [MaterialOrigin.bind_ok_ambient] using tail)


theorem TxCryptInventory.enqueue (crypt : TxCryptInventory active w)
    (owned : TxInventory (⟨.unpublished,pid,items⟩ :: locals) w)
    (device : w.dev = some d) (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid items).run w).run a = .ok ((ret,v),b)) :
    TxCryptInventory active v := by
  have queues := enqueue_queue_effect pid items a b run
  have disjoint : ∀ id ∈ items, id ∉ (txCryptItems w ++ active).flatten := by
    intro id member previous
    obtain ⟨batch,queued,contains⟩ := List.mem_flatten.mp previous
    obtain ⟨q,p,found,inQueue⟩ := crypt.owners batch queued
    exact owned.localsSeparate q p found id (by simp [txLocalItems,member])
      (List.mem_flatten.mpr ⟨batch,inQueue,contains⟩)
  have oldMarks : ∀ batch ∈ txCryptItems w ++ active, ∃ first,
      batch.head? = some first ∧ TxDisposition.HeadState first .uncrypted v := by
    intro batch member
    obtain ⟨first,head,packet,resident,state⟩ := crypt.uncrypted batch member
    have outside : first ∉ items := by
      intro fresh
      exact disjoint first fresh (List.mem_flatten.mpr ⟨batch,member,List.mem_of_head? head⟩)
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (TxDisposition.MarkTransport.enqueue_other first pid items outside) w a ret v b run
    exact ⟨first,head,packet,same.trans resident,state⟩
  have firstMark : ∃ first, items.head? = some first ∧ TxDisposition.HeadState first .uncrypted v := by
    cases head : items.head? with
    | none => simp only [enqueuePerDeviceAndPeer,head] at run; cases run
    | some first =>
      obtain ⟨packet,resident⟩ := owned.localResident first
        (by simp [txLocalItems,List.mem_of_head? head])
      exact ⟨first,rfl,enqueue_head_uncrypted head resident pid a b run⟩
  have cell : TxRing.nativeCell w = some (d.ifindex,d.encryptQueue) := by simp [TxRing.nativeCell,device]
  obtain ⟨n,h,physical⟩ := crypt.physical d device
  have effect := TxRing.enqueue_result pid items w v a b ret run
  rw [cell] at effect
  have shape : TxDisposition.LiveFrontier.Physical v ∧
      txCryptItems v = if ret = 0 then txCryptItems w ++ [items] else txCryptItems w := by
    rcases effect with ⟨returned,after⟩ | ⟨returned,after⟩ | ⟨returned,after,_⟩
    · have free := TxRing.enqueue_free pid items cell (returned ▸ run)
      have advanced : TxRing.Refines (PtrRing.init n) (h ++ [.offered items true])
          (d.encryptQueue.produce items) := by
        simpa only [Ring.Journal.step,tryProduce,free,Bool.false_eq_true,ite_false] using physical.step (.offer items)
      have output : TxRing.nativeCell v = some (d.ifindex,d.encryptQueue.produce items) := after
      refine ⟨?_,?_⟩
      · intro e endpoint
        have eq : e.encryptQueue = d.encryptQueue.produce items := by
          have pair : (e.ifindex,e.encryptQueue) = (d.ifindex,d.encryptQueue.produce items) := by
            simpa only [TxRing.nativeCell,endpoint,Option.map_some,Option.some.injEq] using output
          exact congrArg Prod.snd pair
        exact ⟨n,h ++ [.offered items true],eq.symm ▸ advanced⟩
      · have mapped := congrArg (fun cell : Option (Nat × PtrRing (List SkbId)) =>
          (cell.map fun pair => pair.2.items).getD []) output
        have live : txCryptItems v = (d.encryptQueue.produce items).items := by
          simpa only [txCryptItems,TxRing.nativeCell,Option.map_map,Function.comp_def,
            Option.map_some,Option.getD_some] using mapped
        rw [ite_eq_left returned,live,TxDisposition.LiveFrontier.produced_items physical free]
        simp only [txCryptItems,device,Option.map_some,Option.getD_some]
    · have same : TxRing.nativeCell v = TxRing.nativeCell w := after.trans cell.symm
      refine ⟨TxDisposition.LiveFrontier.physical_transport same crypt.physical,?_⟩
      have mapped := congrArg (fun cell : Option (Nat × PtrRing (List SkbId)) =>
        (cell.map fun pair => pair.2.items).getD []) same
      have nonzero : ret ≠ 0 := by rw [returned]; decide
      simpa only [ite_eq_right nonzero,txCryptItems,TxRing.nativeCell,Option.map_map,Function.comp_def] using mapped
    · have same : TxRing.nativeCell v = TxRing.nativeCell w := after.trans cell.symm
      refine ⟨TxDisposition.LiveFrontier.physical_transport same crypt.physical,?_⟩
      have mapped := congrArg (fun cell : Option (Nat × PtrRing (List SkbId)) =>
        (cell.map fun pair => pair.2.items).getD []) same
      have nonzero : ret ≠ 0 := by rw [returned]; decide
      simpa only [ite_eq_right nonzero,txCryptItems,TxRing.nativeCell,Option.map_map,Function.comp_def] using mapped
  refine ⟨shape.1,?_,?_,?_⟩
  · rw [shape.2]
    split
    · have freshUnique : items.Nodup := (List.nodup_append.mp owned.localUnique).1
      have all : (items ++ (txCryptItems w ++ active).flatten).Nodup :=
        List.nodup_append.mpr ⟨freshUnique,crypt.unique,fun id member other old eq =>
          disjoint id member (eq ▸ old)⟩
      have perm : ((txCryptItems w ++ [items]) ++ active).Perm (items :: (txCryptItems w ++ active)) := by
        simpa only [List.singleton_append,List.cons_append,List.nil_append,List.append_assoc] using
          (show (txCryptItems w ++ [items]).Perm ([items] ++ txCryptItems w) from List.perm_append_comm).append_right active
      exact perm.flatten.nodup_iff.mpr all
    · exact crypt.unique
  · intro batch member
    rw [shape.2] at member
    split at member
    · rename_i returned
      have cases : batch = items ∨ batch ∈ txCryptItems w ++ active := by
        simpa only [List.mem_append,List.mem_singleton,or_comm,or_left_comm,or_assoc] using member
      rcases cases with rfl | old
      · exact queues.installed (Or.inl returned)
      · exact queues.keeps (crypt.owners batch old)
    · exact queues.keeps (crypt.owners batch member)
  · intro batch member
    rw [shape.2] at member
    split at member
    · have cases : batch = items ∨ batch ∈ txCryptItems w ++ active := by
        simpa only [List.mem_append,List.mem_singleton,or_comm,or_left_comm,or_assoc] using member
      rcases cases with rfl | old
      · exact firstMark
      · exact oldMarks batch old
    · exact oldMarks batch member

end Leanux.Proofs.WG.RetirementSecurity
