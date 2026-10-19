import Leanux.Proofs.WG.Index.StagedFrames
import Leanux.Proofs.WG.Index.SendSource
import Leanux.Proofs.WG.Queues.DecryptCarrier
import Leanux.Proofs.WG.Index.StagingAmbientRulesSource


set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.StagingPreservation
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do
abbrev PeerImage := Nat × Option KeypairId × Option KeypairId × Option KeypairId ×
  Option PeerId × Nat × Bool × Option (Nat × Nat × Nat × Nat) × Key × Nat × Option Endpoint
/-- Primitive contracts for the one owned staging source proof. Cached peer/key
observations are supplied by reads and consumed by the original saved writes. -/
structure Contracts (P : WGWorld → Prop) where
  peer : PeerId → PeerImage → Prop
  key : KeypairId → (Option PeerId × Bool) → Prop
  readPeer : ∀ (pid : PeerId) {α : Type} (next : Peer → WG.M α) (Q : α → WGWorld → Prop),
    (∀ p, peer pid (StagingRich.PeerCell p) → Ensures (next p) P Q) →
    Ensures (getPeer pid >>= next) P Q
  readKey : ∀ (kid : KeypairId) {α : Type} (next : Keypair → WG.M α) (Q : α → WGWorld → Prop),
    (∀ k, key kid (StagingRich.KeyCell k) → Ensures (next k) P Q) →
    Ensures (getKeypair kid >>= next) P Q
  setPeer : ∀ pid p, peer pid (StagingRich.PeerCell p) →
    Ensures (WG.setPeer pid p) P (fun _=>P)
  setKey : ∀ kid k, key kid (StagingRich.KeyCell k) →
    Ensures (WG.setKeypair kid k) P (fun _=>P)
  modify : ∀ (f : Device → Device),
    (∀ d, TimerDiscipline.tableCursor (f d)=TimerDiscipline.tableCursor d) →
    (∀ d, (f d).peers=d.peers) → (∀ d, (f d).keypairs=d.keypairs) →
    (∀ d, TimerDiscipline.sendConfiguration (f d)=TimerDiscipline.sendConfiguration d) →
    Ensures (modifyDev f) P (fun _=>P)
  peerGet : ∀ pid, Ensures (WG.peerGet pid) P (fun _=>P)
  peerPut : ∀ pid, Ensures (WG.peerPut pid) P (fun _=>P)
  keyGet : ∀ kid, Ensures (keypairGet kid) P (fun _=>P)
  release : ∀ kid now, Ensures (keypairPut kid now) P (fun _=>P)
  skb : ∀ {α : Type} (action : SkbM α), Ensures (liftSkb action) P (fun _=>P)
  cpu : ∀ pid, Ensures (cpumaskChooseOnline pid) P (fun _=>P)
variable {P : WGWorld → Prop}


def ambientContracts (c : Contracts P) :
    StagingAmbientRules.Contracts (fun g _=>P g) where
  peer := c.peer
  key := c.key
  readPeer := fun pid {_} next good=> c.readPeer pid next (fun _=>P) good
  readKey := fun kid {_} next good=> c.readKey kid next (fun _=>P) good
  setPeer := c.setPeer
  setKey := c.setKey
  modify := c.modify
  peerGet := c.peerGet
  peerPut := c.peerPut
  keyGet := c.keyGet
  release := c.release
  getTx := fun id=>c.skb (SkbStore.getTx id)
  setTx := fun id f=>c.skb (SkbStore.setTx id f)
  freeTx := fun id=>c.skb (SkbStore.freeTx id)
  newTx := fun pkt=>c.skb (SkbStore.newTx pkt)
  branch := fun site value=>(ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  cmp := fun site value lhs rhs=>(ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (AmbientM.branchCmp site value lhs rhs) P)
  clock := fun site=>(ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (AmbientM.hiddenClock64 site) P)
  peek := fun worker pid=>(ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (AmbientM.peekQueuedUnit worker pid) P)
  queue := fun worker pid=>(ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (AmbientM.recordQueued worker pid) P)
  deviceQueue := fun worker=>(ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (AmbientM.queueDeviceWork worker) P)
  ecn := fun pkt=>(ensures_iff _ _ _).mpr (ipTunnelEcnEncap_wg_variant P pkt)
  cpu := c.cpu
theorem setTx (c : Contracts P) (id : SkbId) (f : DataPacket → DataPacket) :
    Ensures (setTxSkb id f) P (fun _=>P) :=
  (StagingAmbientRules.setTx (ambientContracts c) id f)

theorem freeTx (c : Contracts P) (id : SkbId) :
    Ensures (freeTxSkb id) P (fun _=>P) :=
  (StagingAmbientRules.freeTx (ambientContracts c) id)

theorem newTxSkbs_rule (packets : List DataPacket) (c : Contracts P) :
    Ensures (packets.mapM newTxSkb) P (fun _ => P) :=
  (StagingAmbientRules.newTxSkbs_rule packets (ambientContracts c))

theorem enqueuePerDeviceAndPeer_rule (pid : PeerId) (item : List SkbId) (c : Contracts P) :
    Ensures (enqueuePerDeviceAndPeer pid item) P (fun _ => P) :=
  (StagingAmbientRules.enqueuePerDeviceAndPeer_rule pid item (ambientContracts c))

theorem sendQueuedHandshakeInitiation_rule (pid : PeerId) (retry : Bool) (c : Contracts P) :
    ⦃fun g => ⌜P g⌝⦄ sendQueuedHandshakeInitiation pid retry ⦃⇓? _ g => ⌜P g⌝⦄ :=
  (ensures_iff _ _ _).mp (StagingAmbientRules.sendQueuedHandshakeInitiation_rule pid retry (ambientContracts c))

theorem enqueuePerPeerTx_rule (item : List SkbId) (state : PacketState) (c : Contracts P) :
    ⦃fun g => ⌜P g⌝⦄ enqueuePerPeerTx item state ⦃⇓? _ g => ⌜P g⌝⦄ :=
  (ensures_iff _ _ _).mp (StagingAmbientRules.enqueuePerPeerTx_rule item state (ambientContracts c))

theorem createData_rule (pid : PeerId) (item : List SkbId) (c : Contracts P) :
    ⦃fun g => ⌜P g⌝⦄ createData pid item ⦃⇓? _ g => ⌜P g⌝⦄ :=
  (ensures_iff _ _ _).mp (StagingAmbientRules.createData_rule pid item (ambientContracts c))

theorem stagedFallback_rule (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (invalid : Bool) (c : Contracts P) :
    ⦃fun g => ⌜P g⌝⦄ Config.stagedFallback pid packets key invalid ⦃⇓? _ g => ⌜P g⌝⦄ :=
  (ensures_iff _ _ _).mp (StagingAmbientRules.stagedFallback_rule pid packets key invalid (ambientContracts c))

theorem stagedAfterGet_rule (pid : PeerId) (packets : List Packet) (key : Option KeypairId) (c : Contracts P) :
    ⦃fun g => ⌜P g⌝⦄ Config.stagedAfterGet pid packets key ⦃⇓? _ g => ⌜P g⌝⦄ :=
  (ensures_iff _ _ _).mp (StagingAmbientRules.stagedAfterGet_rule pid packets key (ambientContracts c))

theorem sendStagedPackets_rule (pid : PeerId) (c : Contracts P) :
    Ensures (sendStagedPackets pid) P (fun _ => P) :=
  (StagingAmbientRules.sendStagedPackets_rule pid (ambientContracts c))

end Leanux.Proofs.WG.Index.StagingPreservation
