import Leanux.Proofs.WG.Queues.TxDispositionEndpoints

/-! Existing TX packet records outside a supplied item survive the actual
creation path, including refusal cleanup. This is a concrete normal-source
frame, not initialized batch separation or eventual worker scheduling. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.MarkTransport
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Std.Do

private theorem point {action : WG.M α} (target : SkbId) (h : SameView txPackets action) :
    SameView (fun w=>txPackets w target) action := h.factor (fun p=>p target)

private theorem readPeer (target pid : SkbId) : SameView (fun w=>txPackets w target) (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  exact congrArg (fun w=>txPackets w target) (Peers.getPeer_current pid w v p a b run).1

private theorem readPacket (target id : SkbId) : SameView (fun w=>txPackets w target) (getTxSkb id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  exact congrArg (fun w=>txPackets w target) (Packets.getTxSkb_current id w v p a b run).1

private theorem modify_packet (target : SkbId) (f : Device→Device) (same : ∀d,(f d).txSkbs=d.txSkbs) :
    SameView (fun w=>txPackets w target) (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  cases run
  simp [txPackets,Option.bind_map,Function.comp_def,same]

/-- A different actual setter retains the complete saved packet, not just its mark. -/
theorem set_other (target id : SkbId) (different : id≠target) (f : DataPacket→DataPacket) :
    SameView (fun w=>txPackets w target) (setTxSkb id f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a u v b run
  cases hd:w.dev with
  | none=>simp [setTxSkb,liftSkb_run,hd] at run
  | some d=>
    cases hp:d.txSkbs[id]? with
    | none=>
      simp [setTxSkb,liftSkb_run,SkbStore.setTx,SkbStore.getTx,hd,hp,invariant,AmbientM.invariant] at run
      cases run
    | some p=>
      rw [Packets.setTxSkb_run w a d id p f hd hp] at run
      cases run
      simp [txPackets,Packets.update,hd,Std.TreeMap.getElem?_insert,different]

theorem free_other (target : SkbId) (item : List SkbId) (outside : target∉item) :
    SameView (fun w=>txPackets w target) (freeList item) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a u v b run
  have exactMap := (hoare_iff_run_ambient _ _ _).mp (freeList_wp item (txPackets w)) w a u v b rfl run
  simpa only [outside,ite_false] using congrFun exactMap target

/-- Publication changes only the supplied head. Its source-acquired borrow
and final payment preserve all other packet records even if inputs alias elsewhere. -/
theorem publish_other (target : SkbId) (item : List SkbId) (state : PacketState)
    (outside : target∉item) : SameView (fun w=>txPackets w target) (enqueuePerPeerTx item state) := by
  intro initial
  let P := fun w=>txPackets w target=initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have getter : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h=>h) (fun _ _ h=>h.2)
  change Preserves P _
  unfold enqueuePerPeerTx
  cases head:item.head? with
  | none=>exact ambient (AmbientM.invariant _)
  | some first=>
    have different : first≠target := fun eq=>outside (eq ▸ List.mem_of_head? head)
    simp only
    repeat' first
      | (allocation_release_head getTxSkb; exact (readPacket target _).wp (fun p=>p=initial))
      | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ P)
      | (allocation_release_head peerGet; exact (point target (peerGet_packets _)).wp (fun p=>p=initial))
      | (allocation_release_head peerPut; exact (point target (peerPut_packets _)).wp (fun p=>p=initial))
      | (allocation_release_head getPeer; exact (readPeer target _).wp (fun p=>p=initial))
      | (allocation_release_head setTxSkb; exact (set_other target first different _).wp (fun p=>p=initial))
      | (allocation_release_head cpumaskChooseOnline; exact (point target (cpu_packets _)).wp (fun p=>p=initial))
      | (allocation_release_head modifyDev; apply (modify_packet target _ ?_).wp (fun p=>p=initial); intro d; rfl)
      | (allocation_release_head getDev; unfold getDev)
      | (allocation_release_head branch; exact ambient (AmbientM.branch _ _))
      | (allocation_release_head invariant; exact ambient (AmbientM.invariant _))
      | (allocation_release_head peekQueuedUnit; exact ambient (AmbientM.peekQueuedUnit _ _))
      | (allocation_release_head recordQueued; exact ambient (AmbientM.recordQueued _ _))
      | (allocation_release_head queueDeviceWork; exact ambient (AmbientM.queueDeviceWork _))
      | (allocation_release_lift_from AmbientM; exact ambient _)
      | allocation_release_step
    all_goals exact getter

/-- Both queue-refusal arms and successful publication retain an unrelated
packet. The original mark reset targets only the supplied item's first ID. -/
theorem enqueue_other (target pid : SkbId) (item : List SkbId) (outside : target∉item) :
    SameView (fun w=>txPackets w target) (enqueuePerDeviceAndPeer pid item) := by
  intro initial
  let P := fun w=>txPackets w target=initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have getter : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h=>h) (fun _ _ h=>h.2)
  change Preserves P _
  unfold enqueuePerDeviceAndPeer
  cases head:item.head? with
  | none=>exact ambient (AmbientM.invariant _)
  | some first=>
    have different : first≠target := fun eq=>outside (eq ▸ List.mem_of_head? head)
    simp only
    repeat' first
      | (allocation_release_head setTxSkb; exact (set_other target first different _).wp (fun p=>p=initial))
      | (allocation_release_head getPeer; exact (readPeer target _).wp (fun p=>p=initial))
      | (allocation_release_head setPeer; unfold setPeer)
      | (allocation_release_head cpumaskNextOnlineFrom; unfold cpumaskNextOnlineFrom)
      | (allocation_release_head modifyDev; apply (modify_packet target _ ?_).wp (fun p=>p=initial); intro d; rfl)
      | (allocation_release_head getDev; unfold getDev)
      | (allocation_release_head branch; exact ambient (AmbientM.branch _ _))
      | (allocation_release_head invariant; exact ambient (AmbientM.invariant _))
      | (allocation_release_head peekQueuedUnit; exact ambient (AmbientM.peekQueuedUnit _ _))
      | (allocation_release_head recordQueued; exact ambient (AmbientM.recordQueued _ _))
      | (allocation_release_head queueDeviceWork; exact ambient (AmbientM.queueDeviceWork _))
      | (allocation_release_lift_from AmbientM; exact ambient _)
      | allocation_release_step
    all_goals exact getter

theorem cleanup_other (target pid first : SkbId) (item : List SkbId) (outside : target∉item) :
    SameView (fun w=>txPackets w target) (cleanupSource pid item first) := by
  unfold cleanupSource
  exact (readPacket target first).bind (fun packet=>
    (point target (keyPut_packets (some packet.keypair) false)).bind (fun _=>
      (point target (peerPut_packets (some pid))).bind (fun _=>free_other target item outside)))

/-- Concrete whole createData, including source refusal cleanup and arbitrary
record outcomes. Normal return preserves every packet outside this item. -/
theorem create_other (target pid : SkbId) (item : List SkbId) (outside : target∉item) :
    SameView (fun w=>txPackets w target) (createData pid item) := by
  intro initial
  let P := fun w=>txPackets w target=initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  change Preserves P _
  rw [createSource_factor]
  cases head:item.head? with
  | none=>exact ambient (AmbientM.invariant _)
  | some first=>
    simp only
    repeat' first
      | (allocation_release_head getPeer; exact (readPeer target _).wp (fun p=>p=initial))
      | (allocation_release_head enqueuePerDeviceAndPeer; exact (enqueue_other target pid item outside).wp (fun p=>p=initial))
      | (allocation_release_head enqueuePerPeerTx; exact (publish_other target item _ outside).wp (fun p=>p=initial))
      | (allocation_release_head createTailSource; unfold createTailSource)
      | (allocation_release_head cleanupSource; exact (cleanup_other target pid first item outside).wp (fun p=>p=initial))
      | (allocation_release_head branch; exact ambient (AmbientM.branch _ _))
      | (allocation_release_head invariant; exact ambient (AmbientM.invariant _))
      | (allocation_release_head peekQueuedUnit; exact ambient (AmbientM.peekQueuedUnit _ _))
      | (allocation_release_head recordQueued; exact ambient (AmbientM.recordQueued _ _))
      | (allocation_release_head queueDeviceWork; exact ambient (AmbientM.queueDeviceWork _))
      | (allocation_release_lift_from AmbientM; exact ambient _)
      | allocation_release_step

/-- A saved DEAD/CRYPTED/UNCRYPTED mark is transported by the actual concrete
creation call, with source disjointness stated explicitly. -/
theorem create_head (target pid : SkbId) (item : List SkbId) (outside : target∉item)
    (state : PacketState) : Preserves (HeadState target state) (createData pid item) :=
  (create_other target pid item outside).wp (fun cell=>∃p,cell=some p ∧ p.state=state)

/-- A finite, ordered sequence of actual creation calls retains an unrelated
packet. Duplicates inside or between the new items remain allowed. -/
theorem creates_other (target : SkbId) (calls : List (PeerId × List SkbId))
    (outside : ∀ call∈calls,target∉call.2) :
    SameView (fun w=>txPackets w target)
      (calls.forM fun call=>createData call.1 call.2) := by
  induction calls with
  | nil=>simpa only [List.forM_eq_forM,List.forM_nil] using SameView.pure (fun w=>txPackets w target) PUnit.unit
  | cons call calls ih=>
    simp only [List.forM_eq_forM,List.forM_cons] at *
    exact (create_other target call.1 call.2 (outside call (by simp))).bind
      (fun _=>ih (fun next member=>outside next (by simp [member])))

theorem creates_head (target : SkbId) (calls : List (PeerId × List SkbId))
    (outside : ∀ call∈calls,target∉call.2) (state : PacketState) :
    Preserves (HeadState target state)
      (calls.forM fun call=>createData call.1 call.2) :=
  (creates_other target calls outside).wp (fun cell=>∃p,cell=some p ∧ p.state=state)

/-- The DEAD mark established by an actual full-ring EPIPE path survives
later disjoint creation calls. This does not assert retention of the owning
peer queue through an underfunded cleanup or execution of a future worker. -/
theorem pipe_then_creates (pid : PeerId) (first : SkbId) (rest : List SkbId)
    (d : Device) (p : Peer) (hp : d.peers[pid]?=some p) (live : p.isDead=false)
    (room : p.txQueue.count<MAX_QUEUED_PACKETS) (full : d.encryptQueue.full=true)
    (calls : List (PeerId × List SkbId)) (outside : ∀ call∈calls,first∉call.2) :
    Hoare (do createData pid (first::rest); calls.forM fun call=>createData call.1 call.2)
      (fun w=>w.dev=some d) (fun _=>HeadState first .dead) := by
  apply hoare_bind _ _ (hoare_consequence
    (create_pipe pid first rest d p hp live room full) (fun _ h=>h)
    (fun _ _ h=>h.2.1))
  intro _
  exact creates_head first calls outside .dead

end Leanux.Proofs.WG.Queues.TxDisposition.MarkTransport
