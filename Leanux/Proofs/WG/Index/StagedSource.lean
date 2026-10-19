import Leanux.Proofs.WG.Index.StagingPreservationSource
import Leanux.Proofs.WG.Index.StagedFrames
import Leanux.Proofs.WG.Index.SendSource
import Leanux.Proofs.WG.Queues.DecryptCarrier

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do
namespace StagingRich

def preservationContracts (entry : WGWorld) : StagingPreservation.Contracts (Frame entry) where
  peer := fun pid cell=>peerMap entry pid=some cell
  key := fun kid cell=>keyMap entry kid=some cell
  readPeer := readPeer entry
  readKey := readKey entry
  setPeer := setPeer_rich entry
  setKey := setKey entry
  modify := fun f same peers keys _=>modifyDev_rich entry f same peers keys
  peerGet := fun pid=>peerGet_rich pid entry
  peerPut := peerPut_rich entry
  keyGet := fun kid=>keypairGet_rich kid entry
  release := release entry
  skb := fun a=>liftSkb_rich a entry
  cpu := fun pid=>cpumaskChooseOnline_rich pid entry

theorem newTxSkbs_rich (packets : List DataPacket) (entry : WGWorld) :
    Ensures (packets.mapM newTxSkb) (Frame entry) (fun _ => Frame entry) :=
  StagingPreservation.newTxSkbs_rule packets (preservationContracts entry)

theorem enqueuePerDeviceAndPeer_rich (pid : PeerId) (item : List SkbId) (entry : WGWorld) :
    Ensures (enqueuePerDeviceAndPeer pid item) (Frame entry) (fun _ => Frame entry) :=
  StagingPreservation.enqueuePerDeviceAndPeer_rule pid item (preservationContracts entry)

theorem sendQueuedHandshakeInitiation_rich (pid : PeerId) (retry : Bool) (entry : WGWorld) :
    ⦃fun g => ⌜(Frame entry) g⌝⦄ sendQueuedHandshakeInitiation pid retry ⦃⇓? _ g => ⌜(Frame entry) g⌝⦄ :=
  StagingPreservation.sendQueuedHandshakeInitiation_rule pid retry (preservationContracts entry)

theorem enqueuePerPeerTx_rich (item : List SkbId) (state : PacketState) (entry : WGWorld) :
    ⦃fun g => ⌜(Frame entry) g⌝⦄ enqueuePerPeerTx item state ⦃⇓? _ g => ⌜(Frame entry) g⌝⦄ :=
  StagingPreservation.enqueuePerPeerTx_rule item state (preservationContracts entry)

theorem createData_rich (pid : PeerId) (item : List SkbId) (entry : WGWorld) :
    ⦃fun g => ⌜(Frame entry) g⌝⦄ createData pid item ⦃⇓? _ g => ⌜(Frame entry) g⌝⦄ :=
  StagingPreservation.createData_rule pid item (preservationContracts entry)

theorem stagedFallback_rich (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (invalid : Bool) (entry : WGWorld) :
    ⦃fun g => ⌜(Frame entry) g⌝⦄ Config.stagedFallback pid packets key invalid ⦃⇓? _ g => ⌜(Frame entry) g⌝⦄ :=
  StagingPreservation.stagedFallback_rule pid packets key invalid (preservationContracts entry)

theorem stagedAfterGet_rich (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (entry : WGWorld) :
    ⦃fun g => ⌜(Frame entry) g⌝⦄ Config.stagedAfterGet pid packets key ⦃⇓? _ g => ⌜(Frame entry) g⌝⦄ :=
  StagingPreservation.stagedAfterGet_rule pid packets key (preservationContracts entry)

theorem sendStagedPackets_rich (pid : PeerId) (entry : WGWorld) :
    Ensures (sendStagedPackets pid) (Frame entry) (fun _ => (Frame entry)) :=
  StagingPreservation.sendStagedPackets_rule pid (preservationContracts entry)

open Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem keepalive_rule (pid : PeerId) (P Q : WGWorld → Prop)
    (returns : ∀g, P g → Q g)
    (staged : Ensures (sendStagedPackets pid) P (fun _ => Q))
    (write : ∀g d p mtu, g.dev = some d → d.peers[pid]? = some p → P g →
      P {g with dev := some {d with peers := d.peers.insert pid ({p with staged := p.staged ++ [{mtu := mtu}]})}}) :
    Ensures (sendKeepalive pid) P (fun _ => Q) :=
  StagingAmbientRules.keepalive_rule pid (fun g _=>P g) (fun g _=>Q g)
    (fun g _=>returns g) staged (fun g _=>write g)
    (fun site value=>(ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P))
    ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hiddenAlloc .keepaliveSkb) P))

theorem sendKeepalive_rich (pid : PeerId) (entry : WGWorld) :
    Ensures (sendKeepalive pid) (Frame entry) (fun _ => Frame entry) := by
  apply keepalive_rule pid _ _ (fun _ h => h) (sendStagedPackets_rich pid entry)
  intro g d p mtu hd hp pre
  have cell : peerMap entry pid = some (PeerCell p) :=
    pre.peers pid _ (by simp [peerMap,hd,hp])
  have write := setPeer_rich entry pid {p with staged := p.staged ++ [{mtu := mtu}]} cell
    g ({env := fun _ _ => false,timing := ⟨0,0⟩} : Ambient) () _ ({env := fun _ _ => false,timing := ⟨0,0⟩} : Ambient) pre rfl
  simpa only [hd,Option.map_some] using write

end StagingRich

theorem keypairPut_staging (key : Option KeypairId) (now : Bool) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ keypairPut key now ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := (ensures_iff _ _ _).mp (StagingRich.forget _ (fun e => StagingRich.release e key now) entry)

theorem sendQueuedHandshakeInitiation_staging (pid : PeerId) (retry : Bool) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ sendQueuedHandshakeInitiation pid retry ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := (ensures_iff _ _ _).mp (StagingRich.forget _ (fun e => (ensures_iff _ _ _).mpr (StagingRich.sendQueuedHandshakeInitiation_rich pid retry e)) entry)

theorem enqueuePerPeerTx_staging (item : List SkbId) (state : PacketState) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ enqueuePerPeerTx item state ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := (ensures_iff _ _ _).mp (StagingRich.forget _ (fun e => (ensures_iff _ _ _).mpr (StagingRich.enqueuePerPeerTx_rich item state e)) entry)

theorem createData_staging (pid : PeerId) (item : List SkbId) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ createData pid item ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := (ensures_iff _ _ _).mp (StagingRich.forget _ (fun e => (ensures_iff _ _ _).mpr (StagingRich.createData_rich pid item e)) entry)

theorem stagedFallback_staging (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (invalid : Bool) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ Config.stagedFallback pid packets key invalid ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := (ensures_iff _ _ _).mp (StagingRich.forget _ (fun e => (ensures_iff _ _ _).mpr (StagingRich.stagedFallback_rich pid packets key invalid e)) entry)

theorem stagedAfterGet_staging (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (entry : WGWorld) :
    ⦃fun g => ⌜(StagingFrame entry) g⌝⦄ Config.stagedAfterGet pid packets key ⦃⇓? _ g => ⌜(StagingFrame entry) g⌝⦄ := (ensures_iff _ _ _).mp (StagingRich.forget _ (fun e => (ensures_iff _ _ _).mpr (StagingRich.stagedAfterGet_rich pid packets key e)) entry)

theorem sendStagedPackets_staging (pid : PeerId) (entry : WGWorld) :
    Ensures (sendStagedPackets pid) (StagingFrame entry) (fun _ => (StagingFrame entry)) := (StagingRich.forget _ (fun e => (StagingRich.sendStagedPackets_rich pid e)) entry)

theorem sendKeepalive_staging (pid : PeerId) (entry : WGWorld) :
    Ensures (sendKeepalive pid) (StagingFrame entry) (fun _ => (StagingFrame entry)) := (StagingRich.forget _ (fun e => (StagingRich.sendKeepalive_rich pid e)) entry)

theorem newTxSkbs_staging (packets : List DataPacket) (entry : WGWorld) :
    Ensures (packets.mapM newTxSkb) (StagingFrame entry) (fun _ => StagingFrame entry) := StagingRich.forget _ (StagingRich.newTxSkbs_rich packets) entry

theorem enqueuePerDeviceAndPeer_staging (pid : PeerId) (item : List SkbId) (entry : WGWorld) :
    Ensures (enqueuePerDeviceAndPeer pid item) (StagingFrame entry) (fun _ => StagingFrame entry) := StagingRich.forget _ (StagingRich.enqueuePerDeviceAndPeer_rich pid item) entry

theorem newTxSkbs_tables (packets : List DataPacket) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ packets.mapM newTxSkb ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (newTxSkbs_staging packets))

theorem enqueuePerDeviceAndPeer_tables (pid : PeerId) (item : List SkbId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ enqueuePerDeviceAndPeer pid item ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (enqueuePerDeviceAndPeer_staging pid item))

theorem keypairPut_tables (key : Option KeypairId) (now : Bool) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ keypairPut key now ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (fun entry =>
    (ensures_iff _ _ _).mpr (keypairPut_staging key now entry)))

theorem sendQueuedHandshakeInitiation_tables (pid : PeerId) (retry : Bool) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ sendQueuedHandshakeInitiation pid retry ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (fun entry =>
    (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_staging pid retry entry)))

theorem enqueuePerPeerTx_tables (item : List SkbId) (state : PacketState) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ enqueuePerPeerTx item state ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (fun entry =>
    (ensures_iff _ _ _).mpr (enqueuePerPeerTx_staging item state entry)))

theorem createData_tables (pid : PeerId) (item : List SkbId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ createData pid item ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (fun entry =>
    (ensures_iff _ _ _).mpr (createData_staging pid item entry)))

theorem stagedFallback_tables (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (invalid : Bool) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ Config.stagedFallback pid packets key invalid ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (fun entry =>
    (ensures_iff _ _ _).mpr (stagedFallback_staging pid packets key invalid entry)))

theorem stagedAfterGet_tables (pid : PeerId) (packets : List Packet) (key : Option KeypairId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ Config.stagedAfterGet pid packets key ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (staging_tables _ (fun entry =>
    (ensures_iff _ _ _).mpr (stagedAfterGet_staging pid packets key entry)))

theorem sendStagedPackets_tables (pid : PeerId) :
    Ensures (sendStagedPackets pid) TablesSafeWG (fun _ => TablesSafeWG) :=
  staging_tables _ (sendStagedPackets_staging pid)

theorem sendKeepalive_tables (pid : PeerId) :
    Ensures (sendKeepalive pid) TablesSafeWG (fun _ => TablesSafeWG) :=
  staging_tables _ (sendKeepalive_staging pid)


/-- Staging may delete a peer through its actual release paths. Every surviving
tag is retained, with no table-safety or reference-count precondition. -/
theorem sendStagedPackets_tags_retained (pid : PeerId) :
    ∀ g ambient result final after,
      (((sendStagedPackets pid).run g).run ambient = .ok ((result,final),after)) →
      TagsRetained (responseTagMap g.dev) (responseTagMap final.dev) :=
  staging_tags _ (sendStagedPackets_staging pid)

/-- The original keepalive wrapper performs allocation and staging, and does
not silently create a handshake state edge. Normal deletion remains allowed. -/
theorem sendKeepalive_tags_retained (pid : PeerId) :
    ∀ g ambient result final after,
      (((sendKeepalive pid).run g).run ambient = .ok ((result,final),after)) →
      TagsRetained (responseTagMap g.dev) (responseTagMap final.dev) :=
  staging_tags _ (sendKeepalive_staging pid)

end Leanux.Proofs.WG.Index
