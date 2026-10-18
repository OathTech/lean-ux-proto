import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceWorker

/-! TX publication keeps packet cells resident and retains the actual peer
queues. Its state change and work notification are aliases of existing
occurrences, irrespective of the unpublished batch's caller context. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

def txPresent (w : WGWorld) := fun id : SkbId => (Queues.TxDisposition.txPackets w id).isSome

theorem txPresent_packets (action : WG.M α)
    (same : SameView Queues.TxDisposition.txPackets action) : SameView txPresent action :=
  same.of_factor (fun cells id => (cells id).isSome) txPresent (fun _ => rfl)

theorem setTx_present (id : SkbId) (f : DataPacket → DataPacket) :
    SameView txPresent (setTxSkb id f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  cases device : w.dev with
  | none => simp [setTxSkb,liftSkb_run,device] at run
  | some d =>
    cases packet : d.txSkbs[id]? with
    | none =>
      simp [setTxSkb,liftSkb_run,SkbStore.setTx,SkbStore.getTx,device,packet,
        invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      rw [Packets.setTxSkb_run w a d id p f device packet] at run
      cases run
      funext other
      by_cases same : id = other
      · subst other
        simp [txPresent,Queues.TxDisposition.txPackets,Packets.update,device,packet]
      · simp [txPresent,Queues.TxDisposition.txPackets,Packets.update,device,
          Std.TreeMap.getElem?_insert,same]

theorem publish_tx_present (items : List SkbId) (state : PacketState) :
    SameView txPresent (enqueuePerPeerTx items state) := by
  intro initial
  let P := fun w => txPresent w = initial
  have readPeer (pid : PeerId) : Preserves P (getPeer pid) := getPeer_preserves pid P
  have readPacket (id : SkbId) : Preserves P (getTxSkb id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b before run
    exact (Packets.getTxSkb_current id w v p a b run).1 ▸ before
  have modifyPresent (f : Device → Device) (same : ∀ d, (f d).txSkbs = d.txSkbs) :
      Preserves P (modifyDev f) := by
    unfold modifyDev
    apply hoare_modify
    intro w before
    change txPresent _ = initial
    rw [← before]
    funext id
    simp [txPresent,Queues.TxDisposition.txPackets,Option.bind_map,Function.comp_def,same]
  change Preserves P _
  unfold enqueuePerPeerTx
  simp only [peekQueuedUnit,recordQueued]
  repeat' first
    | (allocation_release_head getPeer; exact readPeer _)
    | (allocation_release_head getTxSkb; exact readPacket _)
    | (allocation_release_head getDev; exact (getDev_sameWGStore.of_factor
        (fun store id => (store.dev.bind fun d => d.txSkbs[id]?).isSome) txPresent (fun _ => rfl)).wp
          (fun s => s = initial))
    | (allocation_release_head peerGet; exact (txPresent_packets _ (Queues.TxDisposition.peerGet_packets _)).wp (fun s => s = initial))
    | (allocation_release_head peerPut; exact (txPresent_packets _ (Queues.TxDisposition.peerPut_packets _)).wp (fun s => s = initial))
    | (allocation_release_head cpumaskChooseOnline; exact (txPresent_packets _ (Queues.TxDisposition.cpu_packets _)).wp (fun s => s = initial))
    | (allocation_release_head setTxSkb; exact (setTx_present _ _).wp (fun s => s = initial))
    | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ P)
    | (allocation_release_head modifyDev; apply modifyPresent; intro d; rfl)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ P)
    | (allocation_release_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) P)
    | allocation_release_step

theorem TxInventory.publish (inventory : TxInventory locals w)
    (items : List SkbId) (state : PacketState) (a b : Ambient)
    (run : ((enqueuePerPeerTx items state).run w).run a = .ok (((),v),b)) : TxInventory locals v := by
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Queues.TxDisposition.publication_queues items state) w a () v b run
  have presence := (ProjectedAction.iff_run_ambient _ _ _).mp (publish_tx_present items state)
    w a () v b run
  apply inventory.transport
  · intro pid p found
    have current : Queues.TxDisposition.txQueues v pid = some p.txQueue := by
      simpa [Queues.TxDisposition.txQueues,PeerBorrow.resident,wgStoreView,peerAt] using
        congrArg (Option.map (·.txQueue)) found
    rw [queues] at current
    change (peerAt w pid).map (·.txQueue) = some p.txQueue at current
    obtain ⟨old,resident,queue⟩ := Option.map_eq_some_iff.mp current
    exact ⟨old,resident,congrArg (fun q => q.all.flatten) queue⟩
  · intro id packet resident
    have point := congrFun presence id
    change (Queues.TxDisposition.txPackets v id).isSome =
      (Queues.TxDisposition.txPackets w id).isSome at point
    rw [resident] at point
    exact Option.isSome_iff_exists.mp point

end Leanux.Proofs.WG.RetirementSecurity
