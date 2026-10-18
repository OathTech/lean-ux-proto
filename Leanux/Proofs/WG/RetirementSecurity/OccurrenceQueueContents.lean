import Leanux.Proofs.WG.RetirementSecurity.OccurrenceKeyFrames

/-! An absent peer contributes no TX queue. This projection permits actual
empty-peer retirement and creation while retaining every nonempty owning
queue, including its order and duplicates. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

def txQueueContents (w : WGWorld) (pid : PeerId) : List (List SkbId) :=
  (handoffTxView w pid).getD []

theorem queueContents_of_exact (same : handoffTxView v = handoffTxView w) :
    txQueueContents v = txQueueContents w := by
  funext pid
  exact congrArg (fun queue => queue.getD []) (congrFun same pid)

theorem queueContents_resident (same : txQueueContents v = txQueueContents w)
    (found : peerAt v pid = some p) (nonempty : p.txQueue.all ≠ []) :
    ∃ old, peerAt w pid = some old ∧ old.txQueue.all = p.txQueue.all := by
  have point := congrFun same pid
  change ((peerAt v pid).map (fun p => p.txQueue.all)).getD [] =
    ((peerAt w pid).map (fun p => p.txQueue.all)).getD [] at point
  rw [found] at point
  cases old : peerAt w pid with
  | none => simp only [old,Option.map_none,Option.map_some,Option.getD_none,Option.getD_some] at point; exact False.elim (nonempty point)
  | some q => exact ⟨q,rfl,by simpa [old] using point.symm⟩

theorem queueContents_peer_put (target : Option PeerId) :
    SameView txQueueContents (peerPut target) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  cases target with
  | none =>
    simp [peerPut,branch,AmbientM.branch] at run
    obtain ⟨rfl,rfl⟩ := run
    rfl
  | some pid =>
    cases device : w.dev with
    | none =>
      simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,
        invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases stored : d.peers[pid]? with
      | none =>
        simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,stored,
          invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        have lift (action : IndexM Unit) : (liftM action : WG.M Unit) = liftIndex action := rfl
        by_cases positive : 0 < p.refcount
        · have nonzero : p.refcount ≠ 0 := by omega
          by_cases final : p.refcount = 1
          all_goals
            simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
              refcountDecAndTest,branch,branchCmp,indexRemove_eq,indexUnhash,
              lift,liftIndex_run,retirePeerUnits,modifyAmbient,
              CounterWindow.branch_run,CounterWindow.branchCmp_run,
              device,stored,positive,nonzero,final,
              StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
              CounterWindow.except_ok_bind,CounterWindow.except_pure,
              invariant,AmbientM.invariant,unsupported,AmbientM.unsupported] at run
          all_goals repeat' first | split at run | contradiction
          all_goals rcases run with ⟨rfl,rfl⟩
          all_goals funext owner
          all_goals by_cases same : pid = owner
          all_goals first
            | (subst owner; simp_all [txQueueContents,handoffTxView,PrevQueue.all])
            | simp [txQueueContents,handoffTxView,device,Std.TreeMap.getElem?_erase,
                Std.TreeMap.getElem?_insert,same]
        · have zero : p.refcount = 0 := by omega
          simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
            refcountDecAndTest,branch,branchCmp,CounterWindow.branch_run,
            CounterWindow.branchCmp_run,device,stored,zero,
            StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
            CounterWindow.except_ok_bind,CounterWindow.except_pure,
            unsupported,AmbientM.unsupported] at run
          cases run

theorem TxQueuedBatch.queueContents (owned : TxQueuedBatch w items)
    (same : txQueueContents v = txQueueContents w) : TxQueuedBatch v items := by
  obtain ⟨pid,p,found,member⟩ := owned
  have nonempty : p.txQueue.all ≠ [] := by intro empty; simp [empty] at member
  obtain ⟨q,resident,queue⟩ := queueContents_resident same.symm found nonempty
  exact ⟨pid,q,resident,queue.symm ▸ member⟩

theorem TxInventory.queueContents (inventory : TxInventory locals w)
    (same : txQueueContents v = txQueueContents w)
    (packets : TxDisposition.txPackets v = TxDisposition.txPackets w) : TxInventory locals v := by
  refine ⟨inventory.localUnique,?_,?_,?_,?_,?_⟩
  · intro pid p found
    by_cases empty : p.txQueue.all = []
    · simp [txPeerItems,empty]
    · obtain ⟨old,resident,queue⟩ := queueContents_resident same found empty
      simpa [txPeerItems,queue] using inventory.queueUnique pid old resident
  · intro pid p other q found otherFound different id member otherMember
    have pne : p.txQueue.all ≠ [] := by intro empty; simp [txPeerItems,empty] at member
    have qne : q.txQueue.all ≠ [] := by intro empty; simp [txPeerItems,empty] at otherMember
    obtain ⟨old,resident,queue⟩ := queueContents_resident same found pne
    obtain ⟨oldQ,residentQ,queueQ⟩ := queueContents_resident same otherFound qne
    exact inventory.peersSeparate pid old other oldQ resident residentQ different id
      (by simpa [txPeerItems,queue] using member) (by simpa [txPeerItems,queueQ] using otherMember)
  · intro pid p found id member queued
    have ne : p.txQueue.all ≠ [] := by intro empty; simp [txPeerItems,empty] at queued
    obtain ⟨old,resident,queue⟩ := queueContents_resident same found ne
    exact inventory.localsSeparate pid old resident id member (by simpa [txPeerItems,queue] using queued)
  · intro id member
    simpa only [packets] using inventory.localResident id member
  · intro pid p found id member
    have ne : p.txQueue.all ≠ [] := by intro empty; simp [txPeerItems,empty] at member
    obtain ⟨old,resident,queue⟩ := queueContents_resident same found ne
    simpa only [packets] using inventory.queueResident pid old resident id
      (by simpa [txPeerItems,queue] using member)

theorem occurrences_queueContents {action : WG.M α}
    (wire : SameView txCryptWire action) (queues : SameView txQueueContents action) :
    Preserves (TxOccurrences locals active) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp wire w a result v b run
  have owners := (ProjectedAction.iff_run_ambient _ _ _).mp queues w a result v b run
  exact ⟨before.1.queueContents owners (congrArg Prod.snd fields),
    before.2.frame_packets (congrArg Prod.fst fields)
      (fun _ owned => owned.queueContents owners) (congrArg Prod.snd fields)⟩

private theorem contents_read_bind (initial : PeerId → List (List SkbId))
    (pid : PeerId) (f : Peer → WG.M α)
    (next : ∀ p, initial pid = p.txQueue.all →
      Preserves (fun w => txQueueContents w = initial) (f p)) :
    Preserves (fun w => txQueueContents w = initial) (getPeer pid >>= f) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,readRun,tail⟩ := run
  obtain ⟨same,clock,d,device,stored⟩ := Origins.getPeer_return pid w u p a c readRun
  subst u
  subst c
  have named : initial pid = p.txQueue.all := by
    rw [← before]
    simp [txQueueContents,handoffTxView,device,stored]
  exact (hoare_iff_run_ambient _ _ _).mp (next p named) w a result v b before tail

private theorem contents_set_saved (initial : PeerId → List (List SkbId))
    (pid : PeerId) (p : Peer) (saved : initial pid = p.txQueue.all) :
    Preserves (fun w => txQueueContents w = initial) (setPeer pid p) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases device : w.dev with
  | none =>
    cases run
    funext other
    simpa [txQueueContents,handoffTxView,modifyDev,device] using congrFun before other
  | some d =>
    cases run
    funext other
    by_cases same : pid = other
    · subst other
      simpa [txQueueContents,handoffTxView,modifyDev,device] using saved.symm
    · simpa [txQueueContents,handoffTxView,modifyDev,device,Std.TreeMap.getElem?_insert,same] using congrFun before other

private theorem contents_modify (initial) (f : Device → Device)
    (peers : ∀ d, (f d).peers = d.peers) :
    Preserves (fun w => txQueueContents w = initial) (modifyDev f) := by
  apply hoare_modify
  intro w before
  change (fun pid => txQueueContents _ pid) = initial
  change (fun pid => txQueueContents w pid) = initial at before
  simpa only [txQueueContents,handoffTxView,Option.bind_map,Function.comp_def,peers] using before

theorem contents_factor {action : WG.M α} (same : SameView handoffTxView action) :
    SameView txQueueContents action := same.factor (fun queues pid => (queues pid).getD [])

macro "occurrence_contents_step " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (env_bind_head getPeer; apply contents_read_bind $initial; intro p saved)
  | (rx_retention_head setPeer; apply contents_set_saved $initial; assumption)
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getKeypair
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a k v b before run
     exact (KeyTimes.getKeypair_return _ w v k a b run).1 ▸ before)
  | (rx_retention_head setKeypair; unfold setKeypair)
  | (rx_retention_head modifyDev; apply contents_modify $initial; intro d; rfl)
  | (rx_retention_head peerPut; exact (queueContents_peer_put _).wp (· = $initial))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM; exact (contents_factor (OccurrenceKeys.index_queues _)).wp (· = $initial))
  | (rx_retention_head getDev; exact (getDev_sameWGStore.of_factor
      (fun s => txQueueContents {dev := s.dev}) txQueueContents (fun _ => rfl)).wp (· = $initial))
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (fun w => txQueueContents w = $initial)
     intro x b
     change Preserves (fun w => txQueueContents w = $initial) _)
  | rx_retention_step)

end Leanux.Proofs.WG.RetirementSecurity
