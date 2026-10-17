import Leanux.Proofs.WG.Origins.CurrentTraffic
import Leanux.Proofs.WG.Origins.ConfiguredReceiveLeaves
import Leanux.Proofs.WG.Packets.RxOriginCuts

/-! Native receive paths preserve configured/current identity on actual normal
returns. Receiving invalidation, key/peer removal and every Stop remain actual. -/
namespace Leanux.Proofs.WG.CurrentRx
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues ConfiguredHandshake ConfiguredReceive CurrentLifecycle CurrentTraffic

private theorem counterValidate_view (kp : KeypairId) (nonce : Nat) :
    SameView ConfiguredIdentity.view (counterValidate kp nonce) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold counterValidate WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,
    Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head getKeypair
       exact (ConfiguredIdentity.getKeypair_view _).wp (fun s => s = initial))
    | (rx_retention_head setKeypair
       exact (ConfiguredIdentity.setKeypair_view _ _).wp (fun s => s = initial))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec ConfiguredIdentity.view (fun s => s = initial)
       intro x b
       change Preserves (fun w => ConfiguredIdentity.view w = initial) _)
    | configured_step initial

theorem counterValidate_preserves (kp : KeypairId) (nonce : Nat)
    (history : List SessionOrigin.Receipt) : Preserves (Inv history) (counterValidate kp nonce) :=
  current_preserves _ (counterValidate_view kp nonce)
    (Origins.Retaining.counterValidate_material kp nonce) history

private theorem decryptPacket_view (pkt : RxPacket) :
    SameView ConfiguredIdentity.view (decryptPacket pkt) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold decryptPacket WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc,invariant]
  repeat' first
    | (rx_retention_head getKeypair
       exact (ConfiguredIdentity.getKeypair_view _).wp (fun s => s = initial))
    | (rx_retention_head setKeypair
       exact (ConfiguredIdentity.setKeypair_view _ _).wp (fun s => s = initial))
    | configured_crypto initial
    | configured_step initial

theorem decryptPacket_preserves (pkt : RxPacket) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (decryptPacket pkt) :=
  current_preserves _ (decryptPacket_view pkt)
    (Origins.Retaining.decryptPacket_material pkt) history

theorem readDecrypt_preserves (id : SkbId) (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (RxOrigin.readDecrypt id) := by
  unfold RxOrigin.readDecrypt getRxSkb
  refine preserves_bind ?_ ?_
  · apply hoare_liftSkb
    intro w d store hi hd
    rcases hi with ⟨configured,current⟩
    constructor
    · simpa only [ConfiguredIdentity.Inv,ConfiguredIdentity.InvExcept,ConfiguredIdentity.view,hd,Option.map_some,
        ConfiguredIdentity.state] using configured
    · intro after ha kid key hk valid
      cases ha
      exact current d hd kid key hk valid
  · intro pkt
    exact preserves_bind (decryptPacket_preserves pkt history) (fun _ => preserves_pure _)

private theorem lookupSrc_view (protocol : Nat) (bytes : List UInt8) :
    SameView ConfiguredIdentity.view (lookupSrc protocol bytes) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupSrc_spec protocol bytes (wgStoreView w)) w ambient result v ambient' rfl hr
  change (wgStoreView v).dev.map ConfiguredIdentity.state =
    (wgStoreView w).dev.map ConfiguredIdentity.state
  cases result with
  | none => change wgStoreView v = wgStoreView w at borrowed; rw [borrowed]
  | some pid =>
    obtain ⟨d,p,hd,hp,_,hv⟩ := borrowed
    simp only [hv,hd,Option.map_some]
    exact congrArg some (ConfiguredIdentity.state_peer_same d pid p
      {p with refcount := p.refcount + 1} hp rfl)

private theorem updateRxStats_view (pid : PeerId) (len : Nat) :
    SameView ConfiguredIdentity.view (updateRxStats pid len) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold updateRxStats
  repeat' configured_step initial

private theorem dishonest_view (why : Dishonest) :
    SameView ConfiguredIdentity.view (dishonest why) := by
  cases why <;> intro initial <;>
    exact ConfiguredIdentity.modifyDev_spec (fun s => s = initial) _ (fun _ => rfl)

theorem consumeDataDone_preserves (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (consumeDataDone pid pkt endpoint) := by
  unfold consumeDataDone WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head setPeerEndpoint
       exact current_preserves _ (ConfiguredReceiveLeaves.setPeerEndpoint_view _ _)
         (Origins.Retaining.of_view (Origins.Retaining.setPeerEndpoint_material _ _)) history)
    | (rx_retention_head receivedWithKeypair; exact receivedWithKeypair_preserves _ _ history)
    | (rx_retention_head sendStagedPackets; exact sendStagedPackets_preserves _ history)
    | (rx_retention_head keepKeyFreshRx; exact keepKeyFreshRx_preserves _ history)
    | (rx_retention_head timersHandshakeComplete
       exact current_preserves _ (ConfiguredReceiveLeaves.timersHandshakeComplete_view _ _)
         (Origins.Retaining.of_view (Origins.Retaining.timersHandshakeComplete_material _ _)) history)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived
       exact current_preserves _ (ConfiguredReceiveLeaves.timersAnyAuthenticatedPacketReceived_view _)
         (Origins.Retaining.of_view (Origins.Retaining.timersAnyAuthenticatedPacketReceived_material _)) history)
    | (rx_retention_head timersTraversal
       exact current_preserves _ (ConfiguredIdentity.timersTraversal_view _)
         (Origins.Retaining.of_view (Origins.Retaining.timersTraversal_material _)) history)
    | (rx_retention_head timersDataReceived
       exact current_preserves _ (ConfiguredReceiveLeaves.timersDataReceived_view _)
         (Origins.Retaining.of_view (Origins.Retaining.timersDataReceived_material _)) history)
    | (rx_retention_head updateRxStats
       exact current_preserves _ (updateRxStats_view _ _)
         (Origins.Retaining.of_view (Origins.Retaining.updateRxStats_material _ _)) history)
    | (rx_retention_head dishonest
       exact current_preserves _ (dishonest_view _)
         (Origins.Retaining.of_view (Origins.Retaining.dishonest_material _)) history)
    | (rx_retention_head lookupSrc
       exact current_preserves _ (lookupSrc_view _ _)
         (Origins.Retaining.of_view (Origins.Retaining.lookupSrc_material _ _)) history)
    | (rx_retention_head inetEcnDecapsulate
       exact current_preserves _
         (ConfiguredIdentity.sameWG (project := id) (inetEcnDecapsulate_sameWGStore _ _ _))
         (Origins.Retaining.of_view (Origins.sameView_of_sameWG (project := id)
           (inetEcnDecapsulate_sameWGStore _ _ _))) history)
    | current_traffic_step history

private theorem enqueuePerDeviceAndPeerRx_view (id : SkbId) :
    SameView ConfiguredIdentity.view (enqueuePerDeviceAndPeerRx id) := by
  intro initial
  change Preserves (fun w => ConfiguredIdentity.view w = initial) _
  unfold enqueuePerDeviceAndPeerRx
  simp (config := {zeta := false}) only [branch,setRxSkb,getRxSkb,queueDeviceWork]
  repeat' first
    | (rx_retention_head liftSkb
       apply hoare_liftSkb
       intro w d store hi hd
       simpa only [ConfiguredIdentity.view,hd,Option.map_some,ConfiguredIdentity.state] using hi)
    | (rx_retention_head cpumaskNextOnlineFrom
       exact (ConfiguredIdentity.sameWG (project := fun w => w)
         (cpumaskNextOnlineFrom_sameStore _)).wp (fun s => s = initial))
    | configured_step initial

/-- The actual admission fallback has no IRQ callback work. Its final payment
uses the general invariant-preservation rule, retaining all source guards. -/
private theorem enqueuePerPeerRx_preserves (id : SkbId) (state : PacketState)
    (history : List SessionOrigin.Receipt) :
    Preserves (Inv history) (enqueuePerPeerRx (pure () : WG.M Unit) id state) := by
  unfold enqueuePerPeerRx getRxSkb
  apply preserves_bind
    (show Preserves (Inv history) (liftSkb (SkbStore.getRx id)) from by current_skb_step history)
  intro pkt
  apply preserves_bind (indexOwner_peerDeref_preserves (.keypair pkt.keypair) (Inv history))
  intro pid
  apply preserves_bind (show Preserves (Inv history) (peerGet pid) from by current_traffic_step history)
  intro _
  apply hoare_bind _ _ (CurrentTraffic.readPeer_spec history pid)
  intro p
  let Q := fun w => Inv history w ∧
    (ConfiguredIdentity.view w).bind (fun s => s.peers pid) = some (ConfiguredIdentity.cell p)
  have write : Preserves Q (setRxSkb id fun q => {q with state}) := by
    unfold setRxSkb
    apply hoare_liftSkb
    intro w d store hi hd
    rcases hi with ⟨⟨configured,current⟩,saved⟩
    refine ⟨⟨?_,?_⟩,?_⟩
    · simpa only [ConfiguredIdentity.Inv,ConfiguredIdentity.InvExcept,ConfiguredIdentity.view,
        hd,Option.map_some,ConfiguredIdentity.state] using configured
    · intro after ha kid key hk valid
      cases ha
      exact current d hd kid key hk valid
    · simpa only [ConfiguredIdentity.view,hd,Option.map_some,ConfiguredIdentity.state] using saved
  have finish : Hoare (do
      setRxSkb id fun q => {q with state}
      setPeer pid {p with napiScheduled := true}
      peerPut (some pid)) Q (fun _ => Inv history) := by
    apply hoare_bind _ _ write
    intro _
    apply hoare_bind _ _ (CurrentTraffic.writePeer_spec history pid {p with napiScheduled := true})
    intro _
    change Preserves (Inv history) (peerPut (some pid))
    current_traffic_step history
  simp only [liftM,monadLift_self,pure_bind]
  split
  · apply hoare_bind _ _ (hoare_liftAmbient
      (AmbientM.invariant "a decrypted packet that is not on its peer's rx_queue") Q)
    intro _
    exact finish
  · exact finish

private theorem indexLookup_preserves (kinds : List IndexKind) (index : Nat)
    (history : List SessionOrigin.Receipt) : Preserves (Inv history) (indexLookup kinds index) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (ConfiguredIdentity.indexLookup_preserves kinds index)
      w ambient result v ambient' hi.1 hr,
    hi.2.retain ((ProjectedAction.iff_run_ambient _ _ _).mp
      (CurrentIdentity.indexLookup_current kinds index) w ambient result v ambient' hr)⟩

theorem consumeData_preserves (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (history : List SessionOrigin.Receipt) : Preserves (Inv history) (consumeData msg src ds) := by
  unfold consumeData WG.orM
  simp (config := {zeta := false}) only [branch,keypairGetNull,invariant,newRxSkb,freeRxSkb]
  repeat' first
    | (rx_retention_head indexLookup; exact indexLookup_preserves _ _ history)
    | (rx_retention_head enqueuePerDeviceAndPeerRx
       exact current_preserves _ (enqueuePerDeviceAndPeerRx_view _)
         (Origins.Retaining.of_view (Origins.Retaining.enqueuePerDeviceAndPeerRx_material _)) history)
    | (rx_retention_head enqueuePerPeerRx; exact enqueuePerPeerRx_preserves _ _ history)
    | current_skb_step history
    | current_traffic_step history

theorem packetReceive_preserves (msg : List UInt8) (src : SkbSource)
    (history : List SessionOrigin.Receipt) : Preserves (Inv history) (packetReceive msg src) := by
  unfold packetReceive cpumaskNextOnline
  simp (config := {zeta := false}) only [branch,queueDeviceWork,unsupported,invariant]
  repeat' first
    | (rx_retention_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp (Inv history))
    | (rx_retention_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp (Inv history))
    | (rx_retention_head consumeData; exact consumeData_preserves _ _ _ history)
    | current_traffic_step history

theorem wgReceive_preserves (msg : List UInt8) (src : SkbSource)
    (history : List SessionOrigin.Receipt) : Preserves (Inv history) (wgReceive msg src) := by
  unfold wgReceive
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (rx_retention_head packetReceive; exact packetReceive_preserves _ _ history)
    | current_traffic_step history

end Leanux.Proofs.WG.CurrentRx
