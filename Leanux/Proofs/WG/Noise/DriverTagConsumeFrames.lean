import Leanux.Proofs.WG.Index.ReceiveCompletionSource
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
    Preserves (Retained entry) (keepKeyFreshRx pid) :=
  Index.ReceiveCompletion.keepKeyFreshRx_preserves_source (Retained entry) pid
    (update entry _ _ (fun _ => rfl)) (queued entry _ _)

theorem handshakeComplete_frame (pid : PeerId) (site : HiddenSite) :
    SameView tagView (timersHandshakeComplete pid site) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  exact ReceptionTagSupport.handshakeComplete_tag_frame pid site g.dev
    g ambient result final after rfl run

theorem timersDataReceived_retained (entry : TagMap) (pid : PeerId) :
    Preserves (Retained entry) (timersDataReceived pid) :=
  Index.ReceiveCompletion.dataReceived_preserves_source (Retained entry) pid
    (modTimer entry _ _ _ _) (update entry _ _ (fun _=>rfl))

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
    Preserves (Retained entry) (RxCredits.prepareRest pid pkt) :=
  Index.ReceiveCompletion.prepareRest_preserves_source (Retained entry) pid pkt
    (keepKeyFreshRx_retained entry pid) (delTimer entry pid .newHandshake)
    (of_frame entry _ (traversal_frame pid)) (timersDataReceived_retained entry pid)
    (fun len => of_frame entry _ (updateRxStats_frame pid len))
    (fun why => of_frame entry _ (dishonest_frame why))
    (fun protocol ds bytes => of_frame entry _
      (store_frame (inetEcnDecapsulate_sameWGStore protocol ds bytes)))

theorem rxFinish_frame (pid : PeerId) (ready : Packets.RxReady) :
    SameView tagView (Packets.rxFinish pid ready) := by
  intro initial
  exact Index.ReceiveCompletion.rxFinish_preserves_source (fun w => tagView w = initial)
    pid ready ((lookupRepay_frame _ _).wp (fun s => s = initial))
    ((dishonest_frame _).wp (fun s => s = initial))
    ((updateRxStats_frame _ _).wp (fun s => s = initial))

theorem afterConfirmation_retained (entry : TagMap) (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    Preserves (Retained entry) (ConsumeConfirmation.afterConfirmation pid pkt confirmed) :=
  Index.ReceiveCompletion.afterConfirmation_preserves_source (Retained entry) pid pkt confirmed
    (of_frame entry _ (handshakeComplete_frame _ _))
    (of_retained entry _ (Index.sendStagedPackets_tags_retained pid))
    (prepareRest_retained entry pid pkt)
    (fun ready => of_frame entry _ (rxFinish_frame pid ready))

theorem consumeDataDone_retained (entry : TagMap) (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Preserves (Retained entry) (consumeDataDone pid pkt endpoint) := by
  rw [ConsumeConfirmation.source]
  exact preserves_bind (of_frame entry _ (setPeerEndpoint_frame pid endpoint)) (fun _ =>
    preserves_bind (of_frame entry _ (receivedWithKeypair_frame pid pkt.keypair))
      (fun confirmed => afterConfirmation_retained entry pid pkt confirmed))


end Leanux.Proofs.WG.Noise.DriverTags.Silent
