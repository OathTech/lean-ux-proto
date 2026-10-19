import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialIngressFields
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialIngressFrames

/-! Actual UDP admission retains crypted RX allocation certificates while
new and rejected cells remain outside that carrier. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.IngressFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects TransmitSecurity Responder Origins.Retaining
set_option maxHeartbeats 600000

theorem key_get (kid : Option KeypairId) : Preserves (Bounded h) (keypairGet kid) :=
  bounded_frame
    (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.keypairGet_geometry) kid).factor Prod.snd)
    (ResidentMaterial.core_of_same (keypairGet_core kid))
    (fun _ => ResidentMaterial.NativeFrames.lower_key_get kid)

theorem enqueue (id : SkbId) : Preserves (Bounded h) (enqueuePerDeviceAndPeerRx id) := by
  unfold enqueuePerDeviceAndPeerRx
  apply preserves_bind (set_state id .uncrypted (by decide))
  intro _
  simp (config := {zeta := false}) only [branch,queueDeviceWork]
  repeat' first
    | (rx_retention_head getRxSkb; exact bounded_read_rx _)
    | (rx_retention_head cpumaskNextOnlineFrom; exact bounded_store (cpumaskNextOnlineFrom_sameStore _))
    | receive_bounded_native_step

theorem receive_publish (id : SkbId) :
    Preserves (Bounded h) (enqueuePerPeerRx (pure () : WG.M Unit) id .dead) := by
  rw [PublicationFrontier.enqueuePerPeerRx_factor]
  exact preserves_bind (publish id .dead (by decide))
    (fun pid => preserves_bind (preserves_pure ()) (fun _ => bounded_peer_put (some pid)))

theorem receive_admit (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves (Bounded h) (consumeData msg src ds) := by
  unfold consumeData WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head indexLookup; exact HandshakeFrames.index_lookup _ _)
    | (allocation_release_head keypairGet; exact key_get _)
    | (allocation_release_head keypairGetNull; exact bounded_store keypairGetNull_sameStore)
    | (allocation_release_head getPeer; exact bounded_read_peer _)
    | (allocation_release_head enqueuePerDeviceAndPeerRx; exact enqueue _)
    | (allocation_release_head enqueuePerPeerRx; exact receive_publish _)
    | (allocation_release_head keypairPut; exact bounded_key_put _ _)
    | (allocation_release_head peerPut; exact bounded_peer_put _)
    | (allocation_release_head freeRxSkb; exact bounded_free_rx _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | allocation_release_step
  all_goals
    apply allocate
    intro eq
    cases eq

theorem cpu_next : Preserves (Bounded h) cpumaskNextOnline := by
  have device := bounded_store (h:=h) getDev_sameWGStore
  have cpu (number : Int) : Preserves (Bounded h)
      (modifyDev fun d => {d with handshakeLastCpu := number}) :=
    bounded_modify_device _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Bounded h) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [cpumaskNextOnline,branch] using [device,cpu,ambient]

theorem packet_receive (msg : List UInt8) (src : SkbSource) :
    Preserves (Bounded h) (packetReceive msg src) := by
  have header := bounded_store (h:=h) ((prepareSkbHeader_sameWGWorld msg).factor wgStoreView)
  have ds (protocol : Nat) (bytes : List UInt8) :=
    bounded_store (h:=h) ((ipTunnelGetDsfield_sameWGWorld protocol bytes).factor wgStoreView)
  have device := bounded_store (h:=h) getDev_sameWGStore
  have append : Preserves (Bounded h)
      (modifyDev fun d => {d with
        handshakeQueue := d.handshakeQueue.produce (msg,src)
        handshakeQueueLen := d.handshakeQueueLen + 1}) :=
    bounded_modify_device _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have data := receive_admit (h:=h) msg src
  have cpu := cpu_next (h:=h)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Bounded h) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [packetReceive,branch,invariant,unsupported,queueDeviceWork]
    using [header,ds,device,append,data,cpu,ambient]

theorem receive (msg : List UInt8) (src : SkbSource) : Preserves (Bounded h) (wgReceive msg src) := by
  have packet := packet_receive (h:=h) msg src
  have ambient {α : Type} (a : AmbientM α) : Preserves (Bounded h) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [wgReceive,branch,unsupported] using [packet,ambient]

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.IngressFrames
