import Leanux.Proofs.WG.RetirementSecurity.TxWorkPublicationSource

/-! Native terminal publication replaces an in-flight encryption service
obligation with the actual guarded owner's queued TX actor. No peer-owner word
immutability or equality to an earlier caller is assumed. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem publication_other (chosen : items.head?=some first) (different : first≠target)
    (state : PacketState) :
    SameView (fun w=>TxDisposition.txPackets w target) (enqueuePerPeerTx items state) := by
  intro initial
  let P := fun w=>TxDisposition.txPackets w target=initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have getter : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2)
  have readPacket (id : SkbId) : Preserves P (getTxSkb id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a packet v b before run
    exact (Packets.getTxSkb_current id w v packet a b run).1 ▸ before
  have write (f : Device→Device) (same : ∀d,(f d).txSkbs=d.txSkbs) :
      Preserves P (modifyDev f) := by
    apply hoare_modify
    intro w before
    simpa only [P,TxDisposition.txPackets,Option.bind_map,Function.comp_def,same] using before
  change Preserves P _
  unfold enqueuePerPeerTx
  simp only [chosen]
  repeat' first
    | (allocation_release_head getTxSkb; exact readPacket _)
    | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ P)
    | (allocation_release_head peerGet; exact ((TxDisposition.peerGet_packets _).factor (fun p=>p target)).wp (fun p=>p=initial))
    | (allocation_release_head peerPut; exact ((TxDisposition.peerPut_packets _).factor (fun p=>p target)).wp (fun p=>p=initial))
    | (allocation_release_head getPeer; exact getPeer_preserves _ P)
    | (allocation_release_head setTxSkb; exact (TxDisposition.MarkTransport.set_other target first different _).wp (fun p=>p=initial))
    | (allocation_release_head cpumaskChooseOnline; exact ((TxDisposition.cpu_packets _).factor (fun p=>p target)).wp (fun p=>p=initial))
    | (allocation_release_head modifyDev
       apply write
       intro d; rfl)
    | (allocation_release_head getDev; unfold getDev)
    | (allocation_release_head branch; exact ambient (AmbientM.branch _ _))
    | (allocation_release_head invariant; exact ambient (AmbientM.invariant _))
    | (allocation_release_head peekQueuedUnit; exact ambient (AmbientM.peekQueuedUnit _ _))
    | (allocation_release_head recordQueued; exact ambient (AmbientM.recordQueued _ _))
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step
  all_goals exact getter

theorem Obligations.publish (before : Obligations (items::crypt) tx w)
    (inventory : TxInventory locals w) (state : PacketState) (terminal : state≠.uncrypted)
    (a b : Ambient)
    (run : ((enqueuePerPeerTx items state).run w).run a=.ok (((),v),b)) :
    Obligations crypt tx v := by
  obtain ⟨selected,owner,ownerPeer,ownerBatch,chosen,ownerFound,ownerMember,ownerHead,scheduled⟩:=
    publication_selected items state a b run
  have selectedState:TxDisposition.HeadState selected state v := by
    cases items with
    | nil=>cases chosen
    | cons id rest=>
      have equal:id=selected := by simpa only [List.head?_cons,Option.some.injEq] using chosen
      subst id
      exact (hoare_iff_run_ambient _ _ _).mp
        (TxDisposition.publication_head selected rest state) w a () v b True.intro run
  have queues:TxDisposition.txQueues v=TxDisposition.txQueues w :=
    (ProjectedAction.iff_run_ambient _ _ _).mp (TxDisposition.publication_queues items state)
      w a () v b run
  have ring:txCryptItems v=txCryptItems w := by
    have same:TxRing.nativeCell v=TxRing.nativeCell w :=
      (ProjectedAction.iff_run_ambient _ _ _).mp (TxRing.enqueuePeer_frame items state) w a () v b run
    simpa only [txCryptItems,TxRing.nativeCell,Option.map_map,Function.comp_def] using
      congrArg (fun cell : Option (Nat × PtrRing (List SkbId))=>
        (cell.map fun pair=>pair.2.items).getD []) same
  have original (q : PeerId) (p : Peer) (found : peerAt v q=some p) :
      ∃old,peerAt w q=some old ∧ p.txQueue.all=old.txQueue.all := by
    have current:TxDisposition.txQueues v q=some p.txQueue := by
      change (peerAt v q).map (·.txQueue)=some p.txQueue
      rw [found]; rfl
    rw [queues] at current
    obtain ⟨old,resident,equal⟩:=Option.map_eq_some_iff.mp current
    exact ⟨old,resident,congrArg (fun queue=>queue.all) equal.symm⟩
  have oldCell (id : SkbId) (different : selected≠id) :
      TxDisposition.txPackets v id=TxDisposition.txPackets w id :=
    (ProjectedAction.iff_run_ambient _ _ _).mp (publication_other chosen different state) w a () v b run
  constructor
  · intro q p found batch member
    obtain ⟨old,stored,contents⟩:=original q p found
    obtain ⟨first,packet,head,resident,pending⟩:=before.batches q old stored batch (contents ▸ member)
    by_cases same:selected=first
    · subst first
      obtain ⟨finalPacket,finalResident,marked⟩:=selectedState
      exact ⟨selected,finalPacket,head,finalResident,fun uncrypted=>(terminal (marked.symm.trans uncrypted)).elim⟩
    · refine ⟨first,packet,head,(oldCell first same).trans resident,?_⟩
      intro uncrypted
      have active:=pending uncrypted
      rw [ring]
      rcases List.mem_append.mp active with live | inFlight
      · exact List.mem_append_left _ live
      · rcases List.mem_cons.mp inFlight with selectedBatch | remaining
        · subst batch
          exact (same (Option.some.inj (chosen.symm.trans head))).elim
        · exact List.mem_append_right _ remaining
  · intro q p found batch first packet queue head resident marked
    obtain ⟨old,stored,contents⟩:=original q p found
    by_cases same:selected=first
    · subst first
      have ownerSame:q=owner := by
        by_cases equal:q=owner
        · exact equal
        · exact False.elim (inventory.peersSeparate q old owner ownerPeer stored ownerFound equal selected
          (List.mem_flatten.mpr ⟨batch,List.mem_of_head? (contents ▸ queue),List.mem_of_head? head⟩)
          (List.mem_flatten.mpr ⟨ownerBatch,ownerMember,List.mem_of_head? ownerHead⟩))
      subst q
      exact List.mem_append_left _ scheduled
    · have pending:=before.heads q old stored batch first packet (contents ▸ queue) head
        ((oldCell first same).symm.trans resident) marked
      rcases List.mem_append.mp pending with pending | active
      · exact List.mem_append_left _ (publication_keeps items state a b run pending)
      · exact List.mem_append_right _ active

end Leanux.Proofs.WG.RetirementSecurity.TxWork
