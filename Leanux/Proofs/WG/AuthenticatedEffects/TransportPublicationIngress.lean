import Leanux.Proofs.WG.AuthenticatedEffects.TransportPublicationIngressFields
import Leanux.Proofs.WG.Packets.PublicationReceive

/-! Native UDP admission preserves the packet authentication carrier: its
allocations and enqueue writes cannot invent a CRYPTED packet. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportPublication
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

private theorem preserves_of_geometry (action : WG.M α)
    (shape : SameView OwnerCompletion.geometry action) (h : List TransportDriver.OriginEvent) :
    Preserves (Inv h) action := preserves_of_rx action (shape.factor Prod.snd) h

theorem store_preserves {action : WG.M α} (frame : SameWGStore action) (h : List TransportDriver.OriginEvent) :
    Preserves (Inv h) action := preserves_of_rx action (store_rx action frame) h

theorem keypairGet_preserves (kid : Option KeypairId) (history : List TransportDriver.OriginEvent) :
    Preserves (Inv history) (keypairGet kid) :=
  preserves_of_geometry _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.keypairGet_geometry) kid) history

theorem indexLookup_preserves (kinds : List IndexKind) (index : Nat)
    (history : List TransportDriver.OriginEvent) : Preserves (Inv history) (indexLookup kinds index) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hi hr
  exact hi.sameRx (RxCredits.loan_rx ((hoare_iff_run_ambient _ _ _).mp
    (RxCredits.indexLookup_loan kinds index w) w ambient result v finalAmbient rfl hr))

private theorem readRx (id : SkbId) (P : WGWorld → Prop) : Preserves P (getRxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a pkt v b hi hr
  exact (Packets.getRxSkb_current id w v pkt a b hr).1 ▸ hi

theorem enqueuePerPeerRx_preserves (irq : WG.M Unit) (id : SkbId) (state : PacketState)
    (notCrypted : state ≠ .crypted) (history : List TransportDriver.OriginEvent)
    (callback : Preserves (Inv history) irq) : Preserves (Inv history) (enqueuePerPeerRx irq id state) := by
  rw [PublicationFrontier.enqueuePerPeerRx_factor]
  exact preserves_bind (publish_noncrypted_preserves id state notCrypted history)
    (fun pid => preserves_bind callback (fun _ => peerPut_preserves (some pid) history))

theorem enqueuePerDeviceAndPeerRx_preserves (id : SkbId) (history : List TransportDriver.OriginEvent) :
    Preserves (Inv history) (enqueuePerDeviceAndPeerRx id) := by
  unfold enqueuePerDeviceAndPeerRx
  apply preserves_bind (setRxSkb_state_preserves id .uncrypted (by decide) history)
  intro _
  apply preserves_of_geometry
  intro initial
  change Preserves (fun w => OwnerCompletion.geometry w = initial) _
  simp (config := {zeta := false}) only [branch,queueDeviceWork]
  repeat' first
    | (allocation_release_head getRxSkb; exact readRx _ _)
    | (allocation_release_head cpumaskNextOnlineFrom
       exact ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.store)
         (cpumaskNextOnlineFrom_sameStore _)).wp (fun s => s = initial))
    | completion_step initial
theorem consumeData_preserves (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (history : List TransportDriver.OriginEvent) : Preserves (Inv history) (consumeData msg src ds) := by
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
private theorem nextCpu (history : List TransportDriver.OriginEvent) :
    Preserves (Inv history) cpumaskNextOnline := by
  unfold cpumaskNextOnline
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head getDev; exact store_preserves getDev_sameWGStore history)
    | (allocation_release_head modifyDev
       apply modifyDev_preserves
       all_goals intros; rfl)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (Inv history))
    | allocation_release_step

theorem packetReceive_preserves (msg : List UInt8) (src : SkbSource)
    (history : List TransportDriver.OriginEvent) : Preserves (Inv history) (WG.packetReceive msg src) := by
  unfold WG.packetReceive
  simp (config := {zeta := false}) only [branch,queueDeviceWork,unsupported,invariant]
  repeat' first
    | (allocation_release_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp (Inv history))
    | (allocation_release_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp (Inv history))
    | (allocation_release_head consumeData; exact consumeData_preserves _ _ _ history)
    | (allocation_release_head getDev; exact store_preserves getDev_sameWGStore history)
    | (allocation_release_head modifyDev
       apply modifyDev_preserves
       all_goals intros; rfl)
    | (allocation_release_head cpumaskNextOnline; exact nextCpu history)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (Inv history))
    | allocation_release_step

theorem wgReceive_preserves (msg : List UInt8) (src : SkbSource)
    (history : List TransportDriver.OriginEvent) : Preserves (Inv history) (WG.wgReceive msg src) := by
  unfold WG.wgReceive
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (allocation_release_head WG.packetReceive; exact packetReceive_preserves _ _ history)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (Inv history))
    | allocation_release_step


end Leanux.Proofs.WG.AuthenticatedEffects.TransportPublication
