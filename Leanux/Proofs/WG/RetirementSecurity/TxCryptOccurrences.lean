import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceStaging
import Leanux.Proofs.WG.Queues.TxLiveStaging

/-! Encryption-ring entries and selected encryption locals alias batches
owned by peer TX queues. Active encryption batches are distinct from the
TX-disposal locals in TxInventory: polling transfers an alias, not ownership.
Only logical live ring entries count; consumed stale physical cells do not. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes
open Queues

def txCryptItems (w : WGWorld) : List (List SkbId) :=
  (w.dev.map fun d => d.encryptQueue.items).getD []

def TxQueuedBatch (w : WGWorld) (items : List SkbId) : Prop :=
  ∃ pid p, peerAt w pid = some p ∧ items ∈ p.txQueue.all

structure TxCryptInventory (active : List (List SkbId)) (w : WGWorld) : Prop where
  physical : TxDisposition.LiveFrontier.Physical w
  unique : (txCryptItems w ++ active).flatten.Nodup
  owners : ∀ items ∈ txCryptItems w ++ active, TxQueuedBatch w items
  uncrypted : ∀ items ∈ txCryptItems w ++ active, ∃ first,
    items.head? = some first ∧ TxDisposition.HeadState first .uncrypted w

theorem TxCryptInventory.selected_unique (inventory : TxCryptInventory (items :: active) w) :
    items.Nodup := by
  have all := (List.nodup_append.mp (by
    simpa only [List.flatten_append] using inventory.unique)).2.1
  exact (List.nodup_append.mp all).1

theorem TxCryptInventory.selected_owned (inventory : TxCryptInventory (items :: active) w) :
    TxQueuedBatch w items := inventory.owners items (by simp)

theorem TxCryptInventory.selected_resident (inventory : TxCryptInventory (items :: active) w)
    (physical : TxInventory locals w) : ∀ id ∈ items,
      ∃ packet, TxDisposition.txPackets w id = some packet := by
  obtain ⟨pid,p,found,queued⟩ := inventory.selected_owned
  intro id member
  exact physical.queueResident pid p found id (List.mem_flatten.mpr ⟨items,queued,member⟩)

theorem TxCryptInventory.selected_uncrypted (inventory : TxCryptInventory (items :: active) w) :
    ∃ first, items.head? = some first ∧ TxDisposition.HeadState first .uncrypted w :=
  inventory.uncrypted items (by simp)

theorem TxCryptInventory.selected_disjoint (inventory : TxCryptInventory (items :: active) w)
    (id : SkbId) (member : id ∈ items) : id ∉ (txCryptItems w ++ active).flatten := by
  have perm : (txCryptItems w ++ items :: active).Perm (items :: (txCryptItems w ++ active)) := by
    simpa only [List.singleton_append,List.append_assoc,List.cons_append,List.nil_append] using
      (show (txCryptItems w ++ [items]).Perm ([items] ++ txCryptItems w) from List.perm_append_comm).append_right active
  have unique := perm.flatten.nodup_iff.mp inventory.unique
  intro other
  exact (List.nodup_append.mp unique).2.2 id member id other rfl

theorem initial_tx_crypt_inventory (net bare : Bool) :
    TxCryptInventory [] (Runner.initialWG net bare) := by
  have emptyRing (n : Nat) : (PtrRing.init (α := List SkbId) n).items = [] := by
    have physical : TxRing.Refines (PtrRing.init n) [] (PtrRing.init n) := ⟨[],rfl⟩
    simpa only [Ring.Journal.admitted,Ring.Journal.consumed,List.filterMap_nil,List.nil_append] using
      physical.initialized.2.1.symm
  have empty : txCryptItems (Runner.initialWG net bare) = [] := by
    have cell : TxRing.nativeCell (Runner.initialWG net bare) =
        if net && !bare then some (3,PtrRing.init MAX_QUEUED_PACKETS) else none := by
      unfold TxRing.nativeCell Runner.initialWG
      split <;> rfl
    have mapped := congrArg
      (fun cell : Option (Nat × PtrRing (List SkbId)) => (cell.map fun pair => pair.2.items).getD []) cell
    have projected : txCryptItems (Runner.initialWG net bare) =
        (if net && !bare then (PtrRing.init MAX_QUEUED_PACKETS).items else []) := by
      split <;> rename_i guard
      all_goals simpa only [TxRing.nativeCell,txCryptItems,Option.map_map,Function.comp_def,
        guard,Bool.false_eq_true,ite_true,ite_false,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none] using mapped
    rw [projected,emptyRing]
    split <;> rfl
  refine ⟨(TxDisposition.LiveFrontier.initial_ready net bare).2,?_,?_,?_⟩
  · simp [empty]
  · intro items member; simp [empty] at member
  · intro items member; simp [empty] at member

/-- A complete native ring poll moves precisely its live logical head into
an explicit encryption local. It does not move peer-queue ownership and
cannot select a packet already active in another encryption continuation. -/
theorem TxCryptInventory.poll (inventory : TxCryptInventory active w)
    (a b : Ambient)
    (run : ((TxRing.pollSource).run w).run a = .ok ((out,v),b)) :
    TxCryptInventory (out.toList ++ active) v := by
  cases device : w.dev with
  | none => simp [TxRing.pollSource,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    obtain ⟨n,h,physical⟩ := inventory.physical d device
    have cell : TxRing.nativeCell w = some (d.ifindex,d.encryptQueue) := by simp [TxRing.nativeCell,device]
    obtain ⟨selected,installed⟩ := TxRing.poll_result cell run
    have before := physical.initialized.2.1
    have after := (physical.step .poll).initialized.2.1
    simp only [Ring.Journal.step,Ring.Journal.admitted,Ring.Journal.consumed,
      List.filterMap_append,List.filterMap_cons,List.filterMap_nil,List.append_nil] at after
    change Ring.Journal.admitted h = (Ring.Journal.consumed h ++ d.encryptQueue.consume.1.toList) ++
      d.encryptQueue.consume.2.items at after
    rw [before,List.append_assoc] at after
    have sequence : d.encryptQueue.items = out.toList ++ d.encryptQueue.consume.2.items := by
      simpa only [selected] using List.append_cancel_left after
    have geometry : StagingOccurrences.geometry v = StagingOccurrences.geometry w := by
      have frame : SameView StagingOccurrences.geometry TxRing.pollSource := by
        intro initial
        change Preserves (fun w => StagingOccurrences.geometry w = initial) _
        unfold TxRing.pollSource
        repeat' first
          | (allocation_release_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
          | staging_geometry_step initial
      exact (ProjectedAction.iff_run_ambient _ _ _).mp frame w a out v b run
    have points : ownershipPointView v = ownershipPointView w := by
      have frame : SameView ownershipPointView TxRing.pollSource := by
        intro initial
        change Preserves (fun w => ownershipPointView w = initial) _
        unfold TxRing.pollSource
        repeat' ownership_source_step initial
      exact (ProjectedAction.iff_run_ambient _ _ _).mp frame w a out v b run
    have live : txCryptItems v = d.encryptQueue.consume.2.items := by
      have ring := congrArg (fun cell => (cell.map fun pair => pair.2.items).getD []) installed
      simpa only [TxRing.nativeCell,txCryptItems,Option.map_map,Function.comp_def,Option.map_some,Option.getD_some] using ring
    have old : txCryptItems w = d.encryptQueue.items := by simp [txCryptItems,device]
    have transfer : (txCryptItems v ++ (out.toList ++ active)).Perm (txCryptItems w ++ active) := by
      rw [live,old,sequence]
      simpa only [List.append_assoc] using
        (show (d.encryptQueue.consume.2.items ++ out.toList).Perm (out.toList ++ d.encryptQueue.consume.2.items) from List.perm_append_comm).append_right active
    have owners : ∀ items, TxQueuedBatch w items → TxQueuedBatch v items := by
      intro items owned
      obtain ⟨pid,p,found,queued⟩ := owned
      have point := congrFun (congrArg (fun view => view.2.2.1) points) pid
      change (peerAt v pid).map peerOwnership = (peerAt w pid).map peerOwnership at point
      rw [found] at point
      obtain ⟨q,resident,fields⟩ := Option.map_eq_some_iff.mp point
      have queue : q.txQueue.all = p.txQueue.all := congrArg (fun fields : PeerOwnership => fields.2.1) fields
      exact ⟨pid,q,resident,queue.symm ▸ queued⟩
    refine ⟨?_,transfer.flatten.nodup_iff.mpr inventory.unique,?_,?_⟩
    · intro e endpoint
      have eq : e.encryptQueue = d.encryptQueue.consume.2 := by
        have pair : (e.ifindex,e.encryptQueue) = (d.ifindex,d.encryptQueue.consume.2) := by
          simpa only [TxRing.nativeCell,endpoint,Option.map_some,Option.some.injEq] using installed
        exact congrArg Prod.snd pair
      rw [eq]
      exact ⟨n,h ++ [.polled d.encryptQueue.consume.1],physical.step .poll⟩
    · intro items member
      exact owners items (inventory.owners items (transfer.mem_iff.mp member))
    · intro items member
      obtain ⟨first,head,p,found,state⟩ := inventory.uncrypted items (transfer.mem_iff.mp member)
      exact ⟨first,head,p,(congrFun (congrArg Prod.snd geometry) first).trans found,state⟩

end Leanux.Proofs.WG.RetirementSecurity
