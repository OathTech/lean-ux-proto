import Leanux.Proofs.WG.Queues.TxLogicalSelection
import Leanux.Proofs.WG.Lifetimes.PacketAllocation
import Leanux.Proofs.WG.Lifetimes.TxAccess

/-! Numeric bounds for live encryption items. Consumed physical slots and
intentional aliases with peer TX queues impose no additional conditions. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

def Bounded (r : PtrRing (List SkbId)) (frontier : Nat) : Prop :=
  ∀item∈r.items,∀id∈item,id<frontier

def Inv (w : WGWorld) : Prop := ∀d,w.dev=some d→Bounded d.encryptQueue d.nextSkb

def ItemBounded (item : List SkbId) (w : WGWorld) : Prop :=
  ∀d,w.dev=some d→∀id∈item,id<d.nextSkb

theorem Bounded.mono (hi : Bounded r n) (le : n≤m) : Bounded r m :=
  fun item live id member=>Nat.lt_of_lt_of_le (hi item live id member) le

theorem produced_items (physical : TxRing.Refines (PtrRing.init n) h r)
    (room : r.full=false) (item : List SkbId) : (r.produce item).items=r.items++[item] := by
  have before := physical.initialized.2.1
  have after := (physical.step (.offer item)).initialized.2.1
  simp only [Ring.Journal.step,tryProduce,room,Bool.false_eq_true,↓reduceIte,
    Ring.Journal.admitted,Ring.Journal.consumed,List.filterMap_append,
    List.filterMap_cons,List.filterMap_nil,List.append_nil] at after
  change Ring.Journal.admitted h ++ [item] = Ring.Journal.consumed h ++ (r.produce item).items at after
  rw [before,List.append_assoc] at after
  exact (List.append_cancel_left after).symm

theorem produce_bounded (physical : TxRing.Refines (PtrRing.init n) h r)
    (room : r.full=false) (hi : Bounded r frontier) (fresh : ∀id∈item,id<frontier) :
    Bounded (r.produce item) frontier := by
  intro old live id member
  rw [produced_items physical room item] at live
  rcases List.mem_append.mp live with prior | added
  · exact hi old prior id member
  · have eq : old=item := by simpa only [List.mem_singleton] using added
    subst old
    exact fresh id member

theorem consume_bounded (physical : TxRing.Refines (PtrRing.init n) h r)
    (hi : Bounded r frontier) : Bounded r.consume.2 frontier := by
  cases head:r.peek with
  | none=>simpa only [PtrRing.consume,head] using hi
  | some item=>
    have consumed : r.consume=(some item,r.discardOne) := by simp only [PtrRing.consume,head]
    have live := LogicalSelection.consumed_live physical consumed
    intro old member id contained
    apply hi old
    · rw [live]
      exact List.mem_cons_of_mem item (by simpa only [consumed] using member)
    · exact contained

theorem initial_ring (n frontier : Nat) : Bounded (PtrRing.init n) frontier := by
  have physical : TxRing.Refines (PtrRing.init n) [] (PtrRing.init n) := ⟨[],rfl⟩
  have empty := physical.initialized.2.1
  simp only [Ring.Journal.admitted,Ring.Journal.consumed,List.filterMap_nil,List.nil_append] at empty
  intro item member
  rw [←empty] at member
  contradiction

theorem initial (net bare : Bool) : Inv (Runner.initialWG net bare) := by
  intro d device
  unfold Runner.initialWG at device
  split at device
  · cases device
    exact initial_ring _ _
  · contradiction

theorem allocator (a : PacketAllocation) : Preserves Inv a.original := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient id v clock hi run
  rw [a.run] at run
  cases hd:w.dev with
  | none=>simp only [hd] at run; contradiction
  | some d=>
    simp only [hd] at run
    cases run
    intro e endpoint
    have eq : e=a.device d := by simpa [Packets.update,hd] using endpoint.symm
    subst e
    cases a <;> exact (hi d hd).mono (Nat.le_succ _)

theorem allocate (packets : List DataPacket) : Preserves Inv (packets.mapM newTxSkb) := by
  apply mapM_view_spec id Inv
  intro packet
  exact allocator (.tx packet)

theorem allocated_item (packets : List DataPacket) (hi : Inv w)
    (run : ((packets.mapM newTxSkb).run w).run a=.ok ((item,v),b)) :
    Inv v ∧ ItemBounded item v := by
  have maintained := (hoare_iff_run_ambient _ _ _).mp (allocate packets) w a item v b hi run
  refine ⟨maintained,?_⟩
  intro e endDevice target member
  cases packets with
  | nil=>simp only [List.mapM_nil] at run; cases run; contradiction
  | cons packet packets=>
    cases hd:w.dev with
    | none=>
      simp only [List.mapM_cons,MaterialOrigin.bind_ok_ambient] at run
      obtain ⟨id,u,clock,head,_⟩ := run
      change ((PacketAllocation.tx packet).original.run w).run a = .ok ((id,u),clock) at head
      rw [PacketAllocation.run (.tx packet),hd] at head
      contradiction
    | some d=>
      obtain ⟨ids,_,last,lastDevice,frontier,_,_⟩ := ItemSeparation.allocate_result (packet::packets) hd run
      have same : e=last := Option.some.inj (endDevice.symm.trans lastDevice)
      subst e
      rw [frontier]
      rw [ids] at member
      exact (List.mem_range'_1.mp member).2

theorem enqueue_metadata (pid : PeerId) (item : List SkbId) :
    SameView allocationMetadata (enqueuePerDeviceAndPeer pid item) := by
  intro initial
  let P := fun w=>allocationMetadata w=initial
  have readPeer (pid : PeerId) : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi run
    simpa only [(Peers.getPeer_current pid w v p a b run).1] using hi
  have getter : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h=>h) (fun _ _ h=>h.2)
  change Preserves P _
  unfold enqueuePerDeviceAndPeer
  simp only [branch,invariant]
  repeat' first
    | (allocation_release_head setTxSkb; exact (setTxSkb_metadata _ _).wp (fun m=>m=initial))
    | (allocation_release_head getPeer; exact readPeer _)
    | (allocation_release_head setPeer; exact (setPeer_metadata _ _).wp (fun m=>m=initial))
    | (allocation_release_head getDev; unfold getDev)
    | (allocation_release_head cpumaskNextOnlineFrom; unfold cpumaskNextOnlineFrom)
    | (allocation_release_head modifyDev; apply (metadata_modifyDev _ ?_).wp (fun m=>m=initial); intro d; rfl)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ P)
    | (allocation_release_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) P)
    | (allocation_release_head queueDeviceWork; exact hoare_liftAmbient (AmbientM.queueDeviceWork _) P)
    | allocation_release_step
  all_goals exact getter

theorem enqueue (pid : PeerId) (item : List SkbId)
    (device : w.dev=some d) (physical : TxRing.Refines (PtrRing.init n) h d.encryptQueue)
    (hi : Inv w) (bounded : ItemBounded item w)
    (run : ((enqueuePerDeviceAndPeer pid item).run w).run a=.ok ((ret,v),b)) : Inv v := by
  have result := TxRing.enqueue_result pid item w v a b ret run
  have metadata := (ProjectedAction.iff_run_ambient _ _ _).mp (enqueue_metadata pid item) w a ret v b run
  intro e atEnd
  obtain ⟨before,old,fields⟩ := allocationMetadata_device metadata atEnd
  have eq : before=d := Option.some.inj (old.symm.trans device)
  subst before
  have frontier : e.nextSkb=d.nextSkb := congrArg DeviceAllocationMetadata.nextPacket fields
  simp only [TxRing.nativeCell,device,atEnd,Option.map_some] at result
  rw [frontier]
  rcases result with ⟨returned,ring⟩ | ⟨_,ring⟩ | ⟨_,ring,_⟩
  · have ringEq : e.encryptQueue=d.encryptQueue.produce item := congrArg Prod.snd (Option.some.inj ring)
    rw [ringEq]
    have cell : TxRing.nativeCell w=some (d.ifindex,d.encryptQueue) := by simp only [TxRing.nativeCell,device,Option.map_some]
    exact produce_bounded physical (TxRing.enqueue_free pid item cell (returned ▸ run)) (hi d device) (bounded d device)
  · have ringEq : e.encryptQueue=d.encryptQueue := congrArg Prod.snd (Option.some.inj ring)
    rw [ringEq]
    exact hi d device
  · have ringEq : e.encryptQueue=d.encryptQueue := congrArg Prod.snd (Option.some.inj ring)
    rw [ringEq]
    exact hi d device

theorem poll (device : w.dev=some d)
    (physical : TxRing.Refines (PtrRing.init n) h d.encryptQueue) (hi : Inv w)
    (run : (TxRing.pollSource.run w).run a=.ok ((item,v),b)) : Inv v := by
  simp [TxRing.pollSource,getDev,device,modifyDev] at run
  rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
  intro e atEnd
  have eq : e={d with encryptQueue:=d.encryptQueue.consume.2} := by simpa [device] using atEnd.symm
  subst e
  exact consume_bounded physical (hi d device)

end Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
