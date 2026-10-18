import Leanux.Proofs.WG.Noise.ConsumeConfirmationSource
import Leanux.Proofs.WG.Origins.HandshakeSources
import Leanux.Proofs.WG.Origins.RetainingLeaves
import Leanux.Proofs.WG.KeyTimes.Receive
set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReceiveCompletion
open Leanux Leanux.WG Noise Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Origins.HandshakeSources

theorem prepareRest_preserves_source (P : WGWorld → Prop) (pid : PeerId) (pkt : RxPacket)
    (fresh : Preserves P (keepKeyFreshRx pid))
    (received : Preserves P (timersAnyAuthenticatedPacketReceived pid))
    (traversal : Preserves P (timersTraversal pid))
    (data : Preserves P (timersDataReceived pid))
    (stats : ∀ len, Preserves P (updateRxStats pid len))
    (dishonest : ∀ why, Preserves P (WG.dishonest why))
    (ecn : ∀ protocol ds bytes, Preserves P (inetEcnDecapsulate protocol ds bytes)) :
    Preserves P (RxCredits.prepareRest pid pkt) := by
  unfold RxCredits.prepareRest WG.andM WG.orM
  material_lower
  repeat' first
    | unfold Preserves
    | (index_material_head keepKeyFreshRx; exact fresh)
    | (index_material_head timersAnyAuthenticatedPacketReceived; exact received)
    | (index_material_head timersTraversal; exact traversal)
    | (index_material_head timersDataReceived; exact data)
    | (index_material_head updateRxStats; exact stats _)
    | (index_material_head WG.dishonest; exact dishonest _)
    | (index_material_head inetEcnDecapsulate; exact ecn _ _ _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_join
    | material_join_use
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem rxFinish_preserves_source (P : WGWorld → Prop) (pid : PeerId) (ready : Packets.RxReady)
    (lookup : Preserves P (RxBorrow.source ready.protocol ready.bytes))
    (dishonest : Preserves P (WG.dishonest .peer))
    (stats : Preserves P (updateRxStats pid (ready.originalLen + MESSAGE_DATA_LEN_0))) :
    Preserves P (Packets.rxFinish pid ready) := by
  rw [← RxCredits.rxFinishSource_eq]
  unfold RxCredits.rxFinishSource
  material_lower
  repeat' first
    | unfold Preserves
    | (index_material_head RxBorrow.source; exact lookup)
    | (index_material_head WG.dishonest; exact dishonest)
    | (index_material_head updateRxStats; exact stats)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem afterConfirmation_preserves_source (P : WGWorld → Prop)
    (pid : PeerId) (pkt : RxPacket) (confirmed : Bool)
    (complete : Preserves P (timersHandshakeComplete pid .walltimeLastHandshakeData))
    (staged : Preserves P (sendStagedPackets pid))
    (prepare : Preserves P (RxCredits.prepareRest pid pkt))
    (finish : ∀ ready, Preserves P (Packets.rxFinish pid ready)) :
    Preserves P (ConsumeConfirmation.afterConfirmation pid pkt confirmed) := by
  unfold ConsumeConfirmation.afterConfirmation
  material_lower
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head timersHandshakeComplete; exact complete)
    | (index_material_head sendStagedPackets; exact staged)
    | (index_material_head RxCredits.prepareRest; exact prepare)
    | (index_material_head Packets.rxFinish; exact finish _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem keepKeyFreshRx_preserves_source (P : WGWorld → Prop) (pid : PeerId)
    (modify : Preserves P (modifyPeer pid fun p => {p with sentLastminuteHandshake := true}))
    (queued : Preserves P (sendQueuedHandshakeInitiation pid false)) :
    Preserves P (keepKeyFreshRx pid) := by
  have reader (target : PeerId) : Preserves P (getPeer target) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b pre run
    have same := (getPeer_normal target w v p a b run).1
    simpa only [same] using pre
  have keyReader (kid : KeypairId) : Preserves P (getKeypair kid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a k v b pre run
    have same := (KeyTimes.getKeypair_return kid w v k a b run).1
    simpa only [same] using pre
  have source : keepKeyFreshRx pid = (do
      if ← branch .rxFreshSentLastminute (← getPeer pid).sentLastminuteHandshake then return
      let current := (← getPeer pid).keypairCurrent
      let send ← WG.andM (branch .rxFreshKeypair current.isSome) do
        let some id := current | invariant "unreachable"
        let k ← getKeypair id
        WG.andM (branch .rxFreshValid k.sending.isValid) do
          WG.andM (branch .rxFreshInitiator k.iAmTheInitiator) do
            branchExpired .rxFreshExpired k.sending.birthdate
              (REJECT_AFTER_TIME - KEEPALIVE_TIMEOUT - REKEY_TIMEOUT)
      if ← branch .rxFreshSend send then
        modifyPeer pid (fun p => {p with sentLastminuteHandshake := true})
        sendQueuedHandshakeInitiation pid false) := by
    simp only [keepKeyFreshRx,RxCredits.modifyPeer_source,bind_assoc] <;> rfl
  rw [source]
  simp (config := {zeta := false}) only [WG.andM,branch,invariant]
  repeat' first
    | (rx_retention_head modifyPeer; exact modify)
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued)
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _).wp P)
    | (rx_retention_head getPeer; exact reader _)
    | (rx_retention_head getKeypair; exact keyReader _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ite; apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
    | rx_retention_step

theorem dataReceived_preserves_source (P : WGWorld → Prop) (pid : PeerId)
    (arm : Preserves P (modPeerTimer .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS))
    (update : Preserves P (modifyPeer pid fun p => {p with timerNeedAnotherKeepalive := true})) :
    Preserves P (timersDataReceived pid) := by
  have device : Preserves P getDev := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    cases hd:w.dev <;> simp [getDev,hd,invariant,AmbientM.invariant] at run
    · cases run
    · obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run; exact pre
  have peer : Preserves P (getPeer pid) :=
    hoare_consequence (getPeer_spec pid P) (fun _ h=>h) (fun _ _ h=>h.1)
  have source : timersDataReceived pid = (do
      if ← branch .timersDataReceivedRunning (← getDev).running then
        if ← branch .timersDataReceivedNotPending !((← getPeer pid).timerPending .sendKeepalive) then
          discard <| modPeerTimer .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS
        else modifyPeer pid fun p=>{p with timerNeedAnotherKeepalive:=true}) := by
    simp only [timersDataReceived,RxCredits.modifyPeer_source]
  rw [source]
  simp (config:={zeta:=false}) only [branch,discard,map_const,Function.comp_def,map_eq_pure_bind]
  repeat' first
    | (rx_retention_head getDev; exact device)
    | (rx_retention_head getPeer; exact peer)
    | (rx_retention_head modPeerTimer; exact arm)
    | (rx_retention_head modifyPeer; exact update)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.Index.ReceiveCompletion
