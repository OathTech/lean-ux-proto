import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextInventory
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceQueueContents

/-! Readiness uses peer-owned logical batches and surviving packet cells.
Queue removal and freeing are permitted; neither can manufacture a ready
member with an empty buffer. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem Inv.transport (before : Inv w)
    (queues : ∀pid p,peerAt v pid=some p→∀items∈p.txQueue.all,
      ∃old,peerAt w pid=some old ∧ items∈old.txQueue.all)
    (packets : ∀id p,TxDisposition.txPackets v id=some p→
      ∃old,TxDisposition.txPackets w id=some old ∧
        (p.state=.crypted→old.state=.crypted) ∧ (old.bytes≠[]→p.bytes≠[])) : Inv v := by
  intro pid p found items member first head crypted
  obtain ⟨old,resident,queued⟩:=queues pid p found items member
  obtain ⟨packet,atHead,mark⟩:=crypted
  obtain ⟨previous,oldHead,wasCrypted,_⟩:=packets first packet atHead
  have complete:=before pid old resident items queued first head ⟨previous,oldHead,wasCrypted mark⟩
  intro id inside pkt cell
  obtain ⟨earlier,earlierCell,_,bytes⟩:=packets id pkt cell
  exact bytes (complete id inside earlier earlierCell)

theorem Inv.contents (before : Inv w) (queues : txQueueContents v=txQueueContents w)
    (packets : TxDisposition.txPackets v=TxDisposition.txPackets w) : Inv v := by
  apply before.transport
  · intro pid p found items member
    obtain ⟨old,resident,same⟩:=queueContents_resident queues found (by intro empty; simp [empty] at member)
    exact ⟨old,resident,same ▸ member⟩
  · intro id p found
    exact ⟨p,by simpa only [packets] using found,fun done=>done,fun nonempty=>nonempty⟩

theorem Inv.wire_queues (before : Inv w) (wire : txCryptWire v=txCryptWire w)
    (queues : handoffTxView v=handoffTxView w) : Inv v :=
  before.contents (queueContents_of_exact queues) (congrArg Prod.snd wire)

theorem frame {action : WG.M α} (queues : SameView txQueueContents action)
    (packets : SameView TxDisposition.txPackets action) : Preserves Inv action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact before.contents ((ProjectedAction.iff_run_ambient _ _ _).mp queues w a result v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp packets w a result v b run)

theorem peer_put (pid : Option PeerId) : Preserves Inv (peerPut pid) :=
  frame (queueContents_peer_put pid) (TxDisposition.peerPut_packets pid)

theorem key_put (kid : Option KeypairId) (now : Bool) : Preserves Inv (keypairPut kid now) :=
  frame ((keypairPut_protect kid now).factor (fun view pid=>(view.2.2.1 pid).getD []))
    (TxDisposition.keyPut_packets kid now)

theorem free_list (items : List SkbId) : Preserves Inv (TxDisposition.freeList items) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have cells:TxDisposition.txPackets v=fun id=>if id∈items then none else TxDisposition.txPackets w id:=
    (hoare_iff_run_ambient _ _ _).mp (TxDisposition.freeList_wp items (TxDisposition.txPackets w))
      w a result v b rfl run
  have queues:handoffTxView v=handoffTxView w:= by
    have frame : SameView handoffTxView (TxDisposition.freeList items) := by
      have leaf (id : SkbId) : SameView handoffTxView (freeTxSkb id) := by
        intro initial
        unfold freeTxSkb
        apply hoare_liftSkb
        intro w d store hi hd
        change handoffTxView _ = initial at hi ⊢
        unfold handoffTxView at hi ⊢
        simpa only [hd,Option.bind_some] using hi
      clear run cells
      induction items with
      | nil => simpa only [TxDisposition.freeList_nil] using SameView.pure handoffTxView ()
      | cons id rest ih =>
        rw [TxDisposition.freeList_cons]
        exact (leaf id).bind fun _=>ih
    exact (ProjectedAction.iff_run_ambient _ _ _).mp frame w a result v b run
  apply before.transport
  · intro pid p found batch member
    obtain ⟨old,resident,same⟩:=queueContents_resident (queueContents_of_exact queues) found
      (by intro empty; simp [empty] at member)
    exact ⟨old,resident,same ▸ member⟩
  · intro id p found
    rw [cells] at found
    dsimp only at found
    split at found
    · cases found
    · exact ⟨p,found,fun done=>done,fun nonempty=>nonempty⟩


theorem read_peer (pid : PeerId) : Preserves Inv (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b before run
  exact (Peers.getPeer_current pid w v p a b run).1 ▸ before

theorem read_packet (id : SkbId) : Preserves Inv (getTxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b before run
  exact (Packets.getTxSkb_current id w v p a b run).1 ▸ before

theorem peer_get (pid : PeerId) : Preserves Inv (peerGet pid) :=
  frame (contents_factor (ownership_queues (peerGet_ownership pid)))
    (TxDisposition.peerGet_packets pid)

theorem cpu (pid : PeerId) : Preserves Inv (cpumaskChooseOnline pid) := by
  apply frame ?_ (TxDisposition.cpu_packets pid)
  exact (TxDisposition.cpu_borrow pid).of_factor
    (fun fields pid=>((fields.1 pid).map PrevQueue.all).getD []) txQueueContents
    (fun w=>by funext pid; simp [txQueueContents,handoffTxView,TxDisposition.borrowView,
      TxDisposition.txQueues,PeerBorrow.resident,wgStoreView,Option.map_map,Function.comp_def])

theorem modify_device (f : Device→Device) (peers : ∀d,(f d).peers=d.peers)
    (packets : ∀d,(f d).txSkbs=d.txSkbs) : Preserves Inv (modifyDev f) := by
  apply frame
  · intro initial
    apply hoare_modify
    intro w before
    change (fun pid=>txQueueContents _ pid) = initial
    change (fun pid=>txQueueContents w pid) = initial at before
    simpa only [txQueueContents,handoffTxView,Option.bind_map,Function.comp_def,peers] using before
  · intro initial
    apply hoare_modify
    intro w before
    change (fun id=>TxDisposition.txPackets _ id) = initial
    change (fun id=>TxDisposition.txPackets w id) = initial at before
    simpa only [TxDisposition.txPackets,Option.bind_map,Function.comp_def,packets] using before

/-- Resetting a mark to a nonready state cannot introduce a ready batch. -/
theorem set_mark (id : SkbId) (state : PacketState) (notReady : state≠.crypted) :
    Preserves Inv (setTxSkb id (fun p=>{p with state})) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases device:w.dev with
  | none=>simp [setTxSkb,liftSkb_run,device] at run
  | some d=>
    cases stored:d.txSkbs[id]? with
    | none=>
      simp [setTxSkb,liftSkb_run,SkbStore.setTx,SkbStore.getTx,device,stored,invariant,AmbientM.invariant] at run
      cases run
    | some old=>
      rw [Packets.setTxSkb_run w a d id old _ device stored] at run
      cases run
      apply before.transport
      · intro pid p found items member
        exact ⟨p,by simpa [peerAt,Packets.update,device] using found,member⟩
      · intro target packet resident
        by_cases same:id=target
        · subst target
          have eq : {old with state:=state}=packet := by
            simpa [TxDisposition.txPackets,Packets.update,device] using resident
          subst packet
          exact ⟨old,by simp [TxDisposition.txPackets,device,stored],fun done=>(notReady done).elim,fun nonempty=>nonempty⟩
        · exact ⟨packet,by simpa [TxDisposition.txPackets,Packets.update,device,Std.TreeMap.getElem?_insert,same] using resident,
            fun done=>done,fun nonempty=>nonempty⟩

theorem publish_not_ready (items : List SkbId) (state : PacketState) (notReady : state≠.crypted) :
    Preserves Inv (enqueuePerPeerTx items state) := by
  have ambient {α : Type} (a : AmbientM α) : Preserves Inv (monadLift a : WG.M α) := hoare_liftAmbient a Inv
  have read : Preserves Inv (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get Inv) (fun _ h=>h) (fun _ _ h=>h.2)
  unfold enqueuePerPeerTx
  cases head:items.head? with
  | none=>exact ambient (AmbientM.invariant _)
  | some first=>
    simp only
    repeat' first
      | (allocation_release_head getTxSkb; exact read_packet _)
      | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ Inv)
      | (allocation_release_head peerGet; exact peer_get _)
      | (allocation_release_head peerPut; exact peer_put _)
      | (allocation_release_head getPeer; exact read_peer _)
      | (allocation_release_head setTxSkb; exact set_mark first state notReady)
      | (allocation_release_head cpumaskChooseOnline; exact cpu _)
      | (allocation_release_head modifyDev; apply modify_device <;> intro d <;> rfl)
      | (allocation_release_head getDev; unfold getDev)
      | (allocation_release_head branch; exact ambient (AmbientM.branch _ _))
      | (allocation_release_head invariant; exact ambient (AmbientM.invariant _))
      | (allocation_release_head peekQueuedUnit; exact ambient (AmbientM.peekQueuedUnit _ _))
      | (allocation_release_head recordQueued; exact ambient (AmbientM.recordQueued _ _))
      | (allocation_release_head queueDeviceWork; exact ambient (AmbientM.queueDeviceWork _))
      | (allocation_release_lift_from AmbientM; exact ambient _)
      | allocation_release_step
    all_goals exact read

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
