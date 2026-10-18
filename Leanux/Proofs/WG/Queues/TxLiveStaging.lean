import Leanux.Proofs.WG.Queues.TxLiveFrontier

/-! The actual staged allocation prefix supplies the numeric input required
by enqueue. Physical ring refinement is carried separately; this does not
assert that peer-queue aliases are disjoint or that a later worker completes. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

def Physical (w : WGWorld) : Prop :=
  ∀d,w.dev=some d→∃n h,TxRing.Refines (PtrRing.init n) h d.encryptQueue

def Ready (w : WGWorld) : Prop := Inv w ∧ Physical w

theorem physical_transport (same : TxRing.nativeCell v=TxRing.nativeCell w)
    (hi : Physical w) : Physical v := by
  intro e endpoint
  cases hd:w.dev with
  | none=>simp [TxRing.nativeCell,endpoint,hd] at same
  | some d=>
    have fields : (e.ifindex,e.encryptQueue)=(d.ifindex,d.encryptQueue) := by
      simpa only [TxRing.nativeCell,endpoint,hd,Option.map_some,Option.some.injEq] using same
    have ringEq : e.encryptQueue=d.encryptQueue := congrArg Prod.snd fields
    rw [ringEq]
    exact hi d hd


theorem allocator_ready (action : PacketAllocation) : Preserves Ready action.original := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a id v b hi run
  refine ⟨(hoare_iff_run_ambient _ _ _).mp (allocator action) w a id v b hi.1 run,?_⟩
  have ring : TxRing.nativeCell v=TxRing.nativeCell w := by
    rw [action.run] at run
    cases hd:w.dev with
    | none=>simp only [hd] at run; contradiction
    | some d=>
      simp only [hd] at run
      cases run
      cases action <;> simp [TxRing.nativeCell,Packets.update,hd,PacketAllocation.device]
  exact physical_transport ring hi.2

theorem poll_ready : Preserves Ready TxRing.pollSource := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a item v b hi run
  cases device:w.dev with
  | none=>simp [TxRing.pollSource,getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d=>
    obtain ⟨n,h,physical⟩ := hi.2 d device
    refine ⟨poll device physical hi.1 run,?_⟩
    intro e endpoint
    have cell : TxRing.nativeCell w=some (d.ifindex,d.encryptQueue) := by
      simp only [TxRing.nativeCell,device,Option.map_some]
    have result := (TxRing.poll_result cell run).2
    have eq : e.encryptQueue=d.encryptQueue.consume.2 := by
      have pair : (e.ifindex,e.encryptQueue)=(d.ifindex,d.encryptQueue.consume.2) := by
        simpa only [TxRing.nativeCell,endpoint,Option.map_some,Option.some.injEq] using result
      exact congrArg Prod.snd pair
    rw [eq]
    exact ⟨n,h++[.polled d.encryptQueue.consume.1],physical.step .poll⟩

/-- Exact source field frames transport this narrow conjunction, including
normal paths which erase peers or packet cells. -/
theorem ready_transport (metadata : allocationMetadata v=allocationMetadata w)
    (ring : TxRing.nativeCell v=TxRing.nativeCell w) (hi : Ready w) : Ready v := by
  refine ⟨?_,physical_transport ring hi.2⟩
  intro e endpoint
  obtain ⟨d,device,fields⟩ := allocationMetadata_device metadata endpoint
  have rq : e.encryptQueue=d.encryptQueue := by
    have pair : (e.ifindex,e.encryptQueue)=(d.ifindex,d.encryptQueue) := by
      simpa only [TxRing.nativeCell,endpoint,device,Option.map_some,Option.some.injEq] using ring
    exact congrArg Prod.snd pair
  rw [rq,show e.nextSkb=d.nextSkb from congrArg DeviceAllocationMetadata.nextPacket fields]
  exact hi.1 d device

theorem initial_ready (net bare : Bool) : Ready (Runner.initialWG net bare) := by
  refine ⟨initial net bare,?_⟩
  intro d device
  unfold Runner.initialWG at device
  split at device
  · cases device
    exact ⟨_,[],⟨[],rfl⟩⟩
  · contradiction

theorem allocation_ring (packets : List DataPacket) :
    SameView TxRing.nativeCell (packets.mapM newTxSkb) := by
  intro initial
  apply mapM_view_spec id (fun w : WGWorld=>TxRing.nativeCell w=initial)
  intro packet
  unfold newTxSkb
  apply hoare_liftSkb
  intro w d store hi hd
  simpa only [id_eq,TxRing.nativeCell,hd,Option.map_some] using hi

theorem allocated_ready (packets : List DataPacket) (hi : Ready w)
    (run : ((packets.mapM newTxSkb).run w).run a=.ok ((item,v),b)) :
    Ready v ∧ ItemBounded item v := by
  have allocated := allocated_item packets hi.1 run
  have ring := (ProjectedAction.iff_run_ambient _ _ _).mp (allocation_ring packets) w a item v b run
  exact ⟨⟨allocated.1,physical_transport ring hi.2⟩,allocated.2⟩

theorem acquire_ready (kid : KeypairId) : Preserves Ready (Affiliation.sendAcquire kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a u v b hi run
  obtain ⟨_,_,_,_,_,_,_,_,_,borrowed⟩ := Affiliation.sendAcquire_certificate kid w v a b run
  obtain ⟨d,p,device,_,_,same⟩ := borrowed
  have next := congrArg WGStoreView.dev same
  change v.dev=some {d with peers:=d.peers.insert _ {p with refcount:=p.refcount+1}} at next
  refine ⟨?_,?_⟩
  · intro e endpoint
    have eq := Option.some.inj (endpoint.symm.trans next)
    subst e
    exact hi.1 d device
  · intro e endpoint
    have eq := Option.some.inj (endpoint.symm.trans next)
    subst e
    exact hi.2 d device

/-- Literal prefix of the existing staged submit action. -/
def stagedAllocate (kid : KeypairId) (packets : List DataPacket) : WG.M (List SkbId) := do
  Affiliation.sendAcquire kid
  packets.mapM newTxSkb

theorem staged_factor (pid kid : Nat) (packets : List DataPacket) :
    RxCredits.stagedSubmit pid kid packets =
      (stagedAllocate kid packets >>= fun item=>createData pid item) := by
  simp only [RxCredits.stagedSubmit,stagedAllocate,bind_assoc]

theorem staged_allocated (kid : KeypairId) (packets : List DataPacket) (hi : Ready w)
    (run : ((stagedAllocate kid packets).run w).run a=.ok ((item,v),b)) :
    Ready v ∧ ItemBounded item v := by
  obtain ⟨u,x,clock,acquired,allocated⟩ := RxCredits.bind_ok_native run
  exact allocated_ready packets
    ((hoare_iff_run_ambient _ _ _).mp (acquire_ready kid) w a u x clock hi acquired) allocated


def Safe (item : List SkbId) (w : WGWorld) : Prop := Ready w ∧ ItemBounded item w

theorem safe_transport (metadata : allocationMetadata v=allocationMetadata w)
    (ring : TxRing.nativeCell v=TxRing.nativeCell w) (hi : Safe item w) : Safe item v := by
  refine ⟨ready_transport metadata ring hi.1,?_⟩
  intro e endpoint id member
  obtain ⟨d,device,fields⟩ := allocationMetadata_device metadata endpoint
  rw [show e.nextSkb=d.nextSkb from congrArg DeviceAllocationMetadata.nextPacket fields]
  exact hi.2 d device id member

theorem frame (item : List SkbId) {action : WG.M α}
    (metadata : SameView allocationMetadata action) (ring : SameView TxRing.nativeCell action) :
    Preserves (Safe item) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact safe_transport
    ((ProjectedAction.iff_run_ambient _ _ _).mp metadata w a result v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp ring w a result v b run) hi

theorem enqueue_safe (pid : PeerId) (item : List SkbId) :
    Preserves (Safe item) (enqueuePerDeviceAndPeer pid item) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a ret v b hi run
  have metadata := (ProjectedAction.iff_run_ambient _ _ _).mp (enqueue_metadata pid item) w a ret v b run
  have old (e : Device) (endpoint : v.dev=some e) := allocationMetadata_device metadata endpoint
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro e endpoint
    obtain ⟨d,device,_⟩ := old e endpoint
    obtain ⟨n,h,physical⟩ := hi.1.2 d device
    exact enqueue pid item device physical hi.1.1 hi.2 run e endpoint
  · intro e endpoint
    obtain ⟨d,device,_⟩ := old e endpoint
    obtain ⟨n,h,physical⟩ := hi.1.2 d device
    have result := TxRing.enqueue_result pid item w v a b ret run
    simp only [TxRing.nativeCell,device,endpoint,Option.map_some] at result
    rcases result with ⟨returned,ring⟩ | ⟨_,ring⟩ | ⟨_,ring,_⟩
    · have ringEq : e.encryptQueue=d.encryptQueue.produce item := congrArg Prod.snd (Option.some.inj ring)
      rw [ringEq]
      have cell : TxRing.nativeCell w=some (d.ifindex,d.encryptQueue) := by simp only [TxRing.nativeCell,device,Option.map_some]
      have room := TxRing.enqueue_free pid item cell (returned ▸ run)
      refine ⟨n,h++[.offered item true],?_⟩
      simpa only [Ring.Journal.step,tryProduce,room,Bool.false_eq_true,↓reduceIte] using physical.step (.offer item)
    · have ringEq : e.encryptQueue=d.encryptQueue := congrArg Prod.snd (Option.some.inj ring)
      rw [ringEq]
      exact ⟨n,h,physical⟩
    · have ringEq : e.encryptQueue=d.encryptQueue := congrArg Prod.snd (Option.some.inj ring)
      rw [ringEq]
      exact ⟨n,h,physical⟩
  · intro e endpoint id member
    obtain ⟨d,device,fields⟩ := old e endpoint
    rw [show e.nextSkb=d.nextSkb from congrArg DeviceAllocationMetadata.nextPacket fields]
    exact hi.2 d device id member

private theorem read_peer (item : List SkbId) (pid : PeerId) : Preserves (Safe item) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  simpa only [(Peers.getPeer_current pid w v p a b run).1] using hi

private theorem read_packet (item : List SkbId) (id : SkbId) : Preserves (Safe item) (getTxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  simpa only [(Packets.getTxSkb_current id w v p a b run).1] using hi

private theorem packet_ring (action : SkbM α) : SameView TxRing.nativeCell (liftSkb action) := by
  intro initial
  apply hoare_liftSkb
  intro w d store hi hd
  simpa only [TxRing.nativeCell,hd,Option.map_some] using hi

private theorem modify_safe (item : List SkbId) (f : Device→Device)
    (metadata : ∀d,deviceAllocationMetadata (f d)=deviceAllocationMetadata d)
    (epoch : ∀d,(f d).ifindex=d.ifindex) (ring : ∀d,(f d).encryptQueue=d.encryptQueue) :
    Preserves (Safe item) (modifyDev f) :=
  frame item (metadata_modifyDev f metadata) (TxRing.modify f epoch ring)

macro "live_safe_step " item:term : tactic => `(tactic| first
  | (allocation_release_head getPeer; exact read_peer $item _)
  | (allocation_release_head getTxSkb; exact read_packet $item _)
  | (allocation_release_head getDev; unfold getDev)
  | (allocation_release_head get; exact hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2))
  | (allocation_release_head setPeer; exact frame $item (setPeer_metadata _ _) (TxRing.setPeer_frame _ _))
  | (allocation_release_head setTxSkb; exact frame $item (setTxSkb_metadata _ _) (packet_ring _))
  | (allocation_release_head peerGet; exact frame $item (peerGet_metadata _) (TxRing.peerGet_frame _))
  | (allocation_release_head peerPut; exact frame $item (peerPut_metadata _) (TxRing.peerPut_frame _))
  | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_head modifyDev; apply modify_safe $item; all_goals intro d; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
  | (allocation_release_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
  | (allocation_release_head ForIn.forIn; apply list_view_spec id (Safe $item); intro x b; change Preserves (Safe $item) _)
  | allocation_release_step)

private theorem cpu_safe (item : List SkbId) (pid : PeerId) :
    Preserves (Safe item) (cpumaskChooseOnline pid) := by
  unfold cpumaskChooseOnline
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' live_safe_step item

private theorem publish_safe (item : List SkbId) (state : PacketState) :
    Preserves (Safe item) (enqueuePerPeerTx item state) := by
  unfold enqueuePerPeerTx
  simp only [peekQueuedUnit,recordQueued]
  repeat' first
    | (allocation_release_head cpumaskChooseOnline; exact cpu_safe item _)
    | live_safe_step item

private theorem free_safe (item : List SkbId) (ids : List SkbId) :
    Preserves (Safe item) (freeList ids) := by
  induction ids with
  | nil=>rw [freeList_nil]; exact preserves_pure _
  | cons id ids ih=>
    rw [freeList_cons]
    apply preserves_bind (frame item ?_ (packet_ring _)) (fun _=>ih)
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    exact (freeTxSkb_retention id w v a b run).metadata

private theorem cleanup_safe (pid first : Nat) (item : List SkbId) :
    Preserves (Safe item) (cleanupSource pid item first) := by
  unfold cleanupSource
  apply preserves_bind (read_packet item first)
  intro packet
  apply preserves_bind (frame item ((keypairPut_rest (some packet.keypair) false).factor (fun x=>x.2.2))
    (TxRing.keypairPut_frame _ _))
  intro _
  exact preserves_bind (frame item (peerPut_metadata _) (TxRing.peerPut_frame _)) (fun _=>free_safe item item)

/-- Every actual createData arm retains the live bound, including both queue
refusals and their real key/peer/packet cleanup. -/
theorem create_safe (pid : PeerId) (item : List SkbId) : Preserves (Safe item) (createData pid item) := by
  rw [createSource_factor]
  repeat' first
    | (allocation_release_head enqueuePerDeviceAndPeer; exact enqueue_safe pid item)
    | (allocation_release_head enqueuePerPeerTx; exact publish_safe item _)
    | (allocation_release_head createTailSource; unfold createTailSource)
    | (allocation_release_head cleanupSource; exact cleanup_safe pid _ item)
    | live_safe_step item

theorem staged_submit (pid kid : Nat) (packets : List DataPacket) :
    Preserves Ready (RxCredits.stagedSubmit pid kid packets) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  rw [staged_factor] at run
  obtain ⟨item,u,clock,allocated,created⟩ := RxCredits.bind_ok_native run
  have ready := staged_allocated kid packets hi allocated
  exact ((hoare_iff_run_ambient _ _ _).mp (create_safe pid item) u clock result v b ready created).1

end Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier
