import Leanux.Proofs.WG.Noise.DriverTagSilentFrames
import Leanux.Proofs.WG.Noise.ConsumeConfirmationSource
import Leanux.Proofs.WG.Noise.RotationEffects
import Leanux.Proofs.WG.Queues.RxBorrow

/-! Native receive completion changes key slots, endpoint, timers and counters,
while every surviving handshake tag retains its entry value. Balanced source
lookup/repayment is projected from its full-peer contract. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Silent
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues TimerDiscipline

theorem rotationRun_tags {pid : PeerId} {d final : Device} {actions : List RotationAction}
    (steps : RotationRun pid d actions final) :
    responseTagMap (some final) = responseTagMap (some d) := by
  induction steps with
  | nil => rfl
  | write d final change p rest resident tail ih =>
    exact ih.trans (tagMap_write d pid p (change.apply p) resident (by cases change <;> rfl))
  | put d middle final key rest release tail ih =>
    apply ih.trans
    funext target
    simp only [responseTagMap,Option.bind_some]
    rw [clearPut_peers release]

theorem receivedWithKeypair_frame (pid : PeerId) (received : KeypairId) :
    SameView tagView (receivedWithKeypair pid received) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  cases device : g.dev with
  | none =>
    simp [receivedWithKeypair,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [receivedWithKeypair,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨out,ending,effect⟩ := receivedWithKeypair_effect pid received d p resident
        g ambient result final after device run
      change responseTagMap final.dev = responseTagMap g.dev
      rw [ending,device]
      by_cases matched : p.keypairNext = some received
      · simp only [ConfirmationEffect,matched,ite_true] at effect
        exact rotationRun_tags effect.2
      · simp only [ConfirmationEffect,matched,ite_false] at effect
        rw [effect.2]

theorem keepKeyFreshRx_retained (entry : TagMap) (pid : PeerId) :
    Preserves (Retained entry) (keepKeyFreshRx pid) := by
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
    | (rx_retention_head modifyPeer; exact update entry _ _ (fun _ => rfl))
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued entry _ _)
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _).wp (Retained entry))
    | silent_native_step entry

theorem handshakeComplete_frame (pid : PeerId) (site : HiddenSite) :
    SameView tagView (timersHandshakeComplete pid site) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  exact ReceptionTagSupport.handshakeComplete_tag_frame pid site g.dev
    g ambient result final after rfl run

theorem timersDataReceived_retained (entry : TagMap) (pid : PeerId) :
    Preserves (Retained entry) (timersDataReceived pid) := by
  unfold timersDataReceived
  simp (config := {zeta := false}) only [branch,discard,map_const,Function.comp_def,map_eq_pure_bind]
  repeat' first
    | (rx_retention_head modPeerTimer; exact modTimer entry _ _ _ _)
    | silent_native_step entry

theorem updateRxStats_frame (pid : PeerId) (len : Nat) :
    SameView tagView (updateRxStats pid len) := by
  change SameView tagView ((modifyDev fun d => {d with rxPackets := d.rxPackets+1,rxBytes := d.rxBytes+len}) >>= fun _ =>
      modifyPeer pid (fun p => {p with rxBytes := p.rxBytes+len}))
  exact (modifyDev_frame
    (fun d : Device => {d with rxPackets := d.rxPackets+1,rxBytes := d.rxBytes+len})
    (fun _ => rfl)).bind (fun _ =>
    modifyPeer_frame pid (fun p => {p with rxBytes := p.rxBytes+len}) (fun _ => rfl))

theorem dishonest_frame (why : Dishonest) : SameView tagView (dishonest why) := by
  cases why <;> exact modifyDev_frame _ (fun _ => rfl)

theorem lookupRepay_frame (protocol : Nat) (bytes : List UInt8) :
    SameView tagView (RxBorrow.source protocol bytes) := by
  apply (RxBorrow.source_frame protocol bytes).of_factor
    (fun s : WGStoreView × (PeerId → Option Peer) => fun pid => (s.2 pid).map Peer.handshakeState)
    tagView
  intro g
  rfl

theorem prepareRest_retained (entry : TagMap) (pid : PeerId) (pkt : RxPacket) :
    Preserves (Retained entry) (RxCredits.prepareRest pid pkt) := by
  unfold RxCredits.prepareRest WG.andM WG.orM
  material_lower
  repeat' first
    | unfold Preserves
    | (index_material_head keepKeyFreshRx; exact keepKeyFreshRx_retained entry _)
    | (index_material_head timersAnyAuthenticatedPacketReceived; exact delTimer entry _ .newHandshake)
    | (index_material_head timersTraversal; exact of_frame entry _ (traversal_frame _))
    | (index_material_head timersDataReceived; exact timersDataReceived_retained entry _)
    | (index_material_head updateRxStats; exact of_frame entry _ (updateRxStats_frame _ _))
    | (index_material_head dishonest; exact of_frame entry _ (dishonest_frame _))
    | (index_material_head inetEcnDecapsulate; exact of_frame entry _
        (store_frame (inetEcnDecapsulate_sameWGStore _ _ _)))
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_join
    | material_join_use
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem rxFinish_frame (pid : PeerId) (ready : Packets.RxReady) :
    SameView tagView (Packets.rxFinish pid ready) := by
  rw [← RxCredits.rxFinishSource_eq]
  intro initial
  change Preserves (fun w => tagView w = initial) _
  unfold RxCredits.rxFinishSource
  material_lower
  repeat' first
    | unfold Preserves
    | (index_material_head RxBorrow.source; exact (lookupRepay_frame _ _).wp (fun s => s = initial))
    | (index_material_head dishonest; exact (dishonest_frame _).wp (fun s => s = initial))
    | (index_material_head updateRxStats; exact (updateRxStats_frame _ _).wp (fun s => s = initial))
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem afterConfirmation_retained (entry : TagMap) (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    Preserves (Retained entry) (ConsumeConfirmation.afterConfirmation pid pkt confirmed) := by
  unfold ConsumeConfirmation.afterConfirmation
  material_lower
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head timersHandshakeComplete; exact of_frame entry _ (handshakeComplete_frame _ _))
    | (index_material_head sendStagedPackets; exact of_retained entry _ (Index.sendStagedPackets_tags_retained _))
    | (index_material_head RxCredits.prepareRest; exact prepareRest_retained entry _ _)
    | (index_material_head Packets.rxFinish; exact of_frame entry _ (rxFinish_frame _ _))
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem consumeDataDone_retained (entry : TagMap) (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Preserves (Retained entry) (consumeDataDone pid pkt endpoint) := by
  rw [ConsumeConfirmation.source]
  exact preserves_bind (of_frame entry _ (setPeerEndpoint_frame pid endpoint)) (fun _ =>
    preserves_bind (of_frame entry _ (receivedWithKeypair_frame pid pkt.keypair))
      (fun confirmed => afterConfirmation_retained entry pid pkt confirmed))


end Leanux.Proofs.WG.Noise.DriverTags.Silent
