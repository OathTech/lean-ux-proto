import Leanux.Proofs.WG.Packets.PublicationIngressNative
import Leanux.Proofs.WG.Packets.PublicationPoll

/-! Concrete receive admission retains existing publication certificates.
Allocation and enqueue write only non-CRYPTED cells. The callback theorem
retains its arbitrary native action with its own preservation contract. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues PublicationCompletion PublicationIdentity

private theorem readRx (id : SkbId) (P : WGWorld → Prop) : Preserves P (getRxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a pkt v b hi hr
  exact (Packets.getRxSkb_current id w v pkt a b hr).1 ▸ hi

theorem publish_noncrypted_preserves (id : SkbId) (state : PacketState)
    (notCrypted : state ≠ .crypted) (history : List RxHistory.Event) :
    Preserves (Inv history) (RxWorkers.publishSource id state) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a pid v b hi hr
  obtain ⟨d,pkt,key,p,hd,_,_,_,_,effect⟩ := publish_execution id state w v a b pid hr
  have hv := congrArg WGStoreView.dev effect
  change v.dev = some _ at hv
  have around := (ProjectedAction.iff_run_ambient _ _ _).mp
    (PublicationHistory.publish_around id state) w a pid v b hr
  have epoch := congrArg Prod.fst around
  have peers := congrArg (fun s => s.2.2) around
  change CurrentIdentity.peerView v = CurrentIdentity.peerView w at peers
  have retained : PeersRetained (CurrentIdentity.peerView w) v := by
    intro q ident hq
    simpa only [peers] using hq
  apply hi.transport_cells
  · intro slot packet cell crypted
    by_cases same : slot = id
    · subst slot
      have selected : packet = {pkt with state} := by
        simpa [RxDisposition.nativeRxStore,hv] using cell.symm
      subst packet
      exact False.elim (notCrypted crypted)
    · have other := congrFun (congrArg (fun s => s.2.1) around) slot
      change (if slot = id then none else (RxDisposition.nativeRxStore v).2 slot) =
        (if slot = id then none else (RxDisposition.nativeRxStore w).2 slot) at other
      rw [ite_eq_right same,ite_eq_right same] at other
      exact ⟨other.symm.trans cell,
        congrArg (fun e : Option Nat => (e.getD 0,slot+1)) epoch⟩
  · exact FrontiersLe.of_eq ((ProjectedAction.iff_run_ambient _ _ _).mp
      (publish_frontier id state) w a pid v b hr)
  · exact peers_fields retained

theorem enqueuePerPeerRx_factor (irq : WG.M Unit) (id : SkbId) (state : PacketState) :
    enqueuePerPeerRx irq id state =
      (RxWorkers.publishSource id state >>= fun pid => irq >>= fun _ => peerPut (some pid)) := by
  simp only [enqueuePerPeerRx,RxWorkers.publishSource,bind_assoc,liftM,monadLift_self]
  repeat' first
    | rfl
    | apply RxWorkers.bind_congr
    | (intro x; try dsimp only)
    | split
    | (simp only [bind_assoc,pure_bind]; done)

theorem enqueuePerPeerRx_preserves (irq : WG.M Unit) (id : SkbId) (state : PacketState)
    (notCrypted : state ≠ .crypted) (history : List RxHistory.Event)
    (callback : Preserves (Inv history) irq) : Preserves (Inv history) (enqueuePerPeerRx irq id state) := by
  rw [enqueuePerPeerRx_factor]
  exact preserves_bind (publish_noncrypted_preserves id state notCrypted history)
    (fun pid => preserves_bind callback (fun _ => peerPut_preserves (some pid) history))

/-- The callback remains an arbitrary product action at the actual IRQ cut. -/
theorem enqueuePerPeerRx_product (irq : Leanux.M Unit) (id : SkbId) (state : PacketState)
    (notCrypted : state ≠ .crypted) (history : List RxHistory.Event)
    (callback : Preserves (fun w : World => Inv history w.wg) irq) :
    Preserves (fun w : World => Inv history w.wg) (enqueuePerPeerRx irq id state) := by
  rw [RxWorkers.enqueue_source]
  apply preserves_bind (PublicationPoll.native_product (Inv history) _
    (publish_noncrypted_preserves id state notCrypted history))
  intro pid
  exact preserves_bind callback (fun _ => PublicationPoll.native_product (Inv history) _
    (peerPut_preserves (some pid) history))

theorem enqueuePerDeviceAndPeerRx_preserves (id : SkbId) (history : List RxHistory.Event) :
    Preserves (Inv history) (enqueuePerDeviceAndPeerRx id) := by
  unfold enqueuePerDeviceAndPeerRx
  apply preserves_bind (setRxSkb_state_preserves id .uncrypted (by decide) history)
  intro _
  apply preserves_of_geometry
  · intro initial
    change Preserves (fun w => OwnerCompletion.geometry w = initial) _
    simp (config := {zeta := false}) only [branch,queueDeviceWork]
    repeat' first
      | (allocation_release_head getRxSkb; exact readRx _ _)
      | (allocation_release_head cpumaskNextOnlineFrom
         exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.store)
           (cpumaskNextOnlineFrom_sameStore _)).wp (fun s => s = initial))
      | completion_step initial
  · intro initial
    simp (config := {zeta := false}) only [branch,queueDeviceWork]
    repeat' first
      | (rx_retention_head getRxSkb; exact readRx _ _)
      | (rx_retention_head cpumaskNextOnlineFrom
         exact (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.configured)
           (ConfiguredIdentity.sameWG (project := fun w => w) (cpumaskNextOnlineFrom_sameStore _)) initial)
      | publication_peer_step initial

theorem consumeData_preserves (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (history : List RxHistory.Event) : Preserves (Inv history) (consumeData msg src ds) := by
  have readPeer (pid : PeerId) : Preserves (Inv history) (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b hi hr
    exact (getPeer_normal pid w v p a b hr).1 ▸ hi
  unfold consumeData WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head indexLookup; exact indexLookup_preserves _ _ history)
    | (allocation_release_head keypairGet; exact keypairGet_preserves _ history)
    | (allocation_release_head keypairGetNull; exact store_preserves keypairGetNull_sameStore history)
    | (allocation_release_head getPeer; exact readPeer _)
    | (allocation_release_head enqueuePerDeviceAndPeerRx; exact enqueuePerDeviceAndPeerRx_preserves _ history)
    | (allocation_release_head enqueuePerPeerRx
       exact enqueuePerPeerRx_preserves _ _ .dead (by decide) history (preserves_pure _))
    | (allocation_release_head keypairPut; exact keypairPut_preserves _ _ history)
    | (allocation_release_head peerPut; exact peerPut_preserves _ history)
    | (allocation_release_head freeRxSkb; exact freeRxSkb_preserves _ history)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (Inv history))
    | allocation_release_step

  all_goals
    apply newRxSkb_preserves
    intro eq
    cases eq

end Leanux.Proofs.WG.PublicationFrontier
