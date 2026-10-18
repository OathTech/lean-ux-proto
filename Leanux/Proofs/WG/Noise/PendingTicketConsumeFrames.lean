import Leanux.Proofs.WG.Noise.PendingTicketTimerFrames
import Leanux.Proofs.WG.Noise.PendingTicketStagingFrames
import Leanux.Proofs.WG.Noise.PendingTicketOptionalClaims
import Leanux.Proofs.WG.Noise.ConfirmationLabelSource
import Leanux.Proofs.WG.KeyTimes.Receive

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Std.Do
open Queues

private theorem peerRead_pending (pid : PeerId) : SameView view (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  exact congrArg view (Origins.getPeer_return pid w v p a b run).1

private theorem keyRead_pending (kid : KeypairId) : SameView view (getKeypair kid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a k v b run
  exact congrArg view (KeyTimes.getKeypair_return kid w v k a b run).1

private theorem retains_wp {α : Type} {a : WG.M α} (ha : RetainsCall a)
    (initial : Store PeerId) : Preserves (fun w => Retained initial (view w)) a :=
  ha.wp (Retained initial) (fun _ _ later earlier => earlier.trans later)

private theorem retains_of_wp {α : Type} {a : WG.M α}
    (ha : ∀ initial, Preserves (fun w => Retained initial (view w)) a) : RetainsCall a := by
  intro initial
  apply hoare_consequence (ha initial)
  · intro w equal
    rw [equal]
    exact Retained.refl _
  · exact fun _ _ h => h

theorem keepKeyFreshRx_retained (pid : PeerId) : RetainsCall (keepKeyFreshRx pid) := by
  apply retains_of_wp
  intro initial
  let P := fun w => Retained initial (view w)
  have peer := (peerRead_pending pid).wp (Retained initial)
  have key := fun kid => (keyRead_pending kid).wp (Retained initial)
  have expired := fun date delay => (branchExpired_sameWGWorld .rxFreshExpired date delay).wp P
  have queued := retains_wp (sendQueuedHandshakeInitiation_retained pid false) initial
  have setter := (modifyPeer_spec_pending_variant pid
    (fun p => {p with sentLastminuteHandshake := true}) (fun _ => rfl)).wp (Retained initial)
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
  change Preserves P _
  simp (config := {zeta := false}) only [WG.andM,branch,invariant]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getPeer; exact peer)
    | (index_material_head getKeypair; exact key _)
    | (index_material_head branchExpired; exact expired _ _)
    | (index_material_head modifyPeer; exact setter)
    | (index_material_head sendQueuedHandshakeInitiation; exact queued)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

theorem updateRxStats_frame (pid : PeerId) (len : Nat) : SameView view (updateRxStats pid len) := by
  change SameView view ((modifyDev fun d => {d with rxPackets := d.rxPackets+1, rxBytes := d.rxBytes+len}) >>= fun _ =>
      modifyPeer pid (fun p => {p with rxBytes := p.rxBytes+len}))
  have first := modifyDev_frame
    (fun d : Device => {d with rxPackets := d.rxPackets+1, rxBytes := d.rxBytes+len})
    (fun _ => rfl) (fun _ => rfl)
  have last := modifyPeer_spec_pending_variant pid (fun p => {p with rxBytes := p.rxBytes+len})
    (fun _ => rfl)
  exact first.bind (fun _ => last)

theorem dishonest_frame (why : Dishonest) : SameView view (dishonest why) := by
  cases why <;> exact modifyDev_frame _ (fun _ => rfl) (fun _ => rfl)

def pendingOfBorrow (s : WGStoreView × (PeerId → Option Peer)) : Store PeerId :=
  ⟨s.1.keypairCounter,fun pid => do
    let p ← s.2 pid
    let kid ← p.keypairNext
    let d ← s.1.dev
    let k ← d.keypairs[kid]?
    pure k.internalId⟩

theorem pending_borrow_factor (w : WGWorld) : view w = pendingOfBorrow (PeerBorrow.view w) := by
  apply Store.ext
  · rfl
  · funext pid
    cases device : w.dev with
    | none => simp [view,pendingOfBorrow,PeerBorrow.view,PeerBorrow.outsidePeers,
        PeerBorrow.resident,wgStoreView,device]
    | some d =>
      cases peer : d.peers[pid]? with
      | none => simp [view,pending,pendingOfBorrow,PeerBorrow.view,PeerBorrow.outsidePeers,
          PeerBorrow.resident,wgStoreView,device,peer]
      | some p =>
        cases next : p.keypairNext <;>
          simp [view,pending,pendingOfBorrow,PeerBorrow.view,PeerBorrow.outsidePeers,
            PeerBorrow.resident,wgStoreView,device,peer,next]

theorem lookupRepay_frame (protocol : Nat) (bytes : List UInt8) :
    SameView view (RxBorrow.source protocol bytes) :=
  (RxBorrow.source_frame protocol bytes).of_factor pendingOfBorrow view pending_borrow_factor

theorem prepareRest_retained (pid : PeerId) (pkt : RxPacket) :
    RetainsCall (RxCredits.prepareRest pid pkt) := by
  apply retains_of_wp
  intro initial
  let P := fun w => Retained initial (view w)
  change Preserves P _
  unfold RxCredits.prepareRest WG.andM WG.orM
  material_lower
  repeat' first
    | unfold Preserves
    | (index_material_head keepKeyFreshRx; exact retains_wp (keepKeyFreshRx_retained _) initial)
    | (index_material_head timersAnyAuthenticatedPacketReceived; exact
        (timersAnyAuthenticatedPacketReceived_frame _).wp (Retained initial))
    | (index_material_head timersTraversal; exact (timersTraversal_frame _).wp (Retained initial))
    | (index_material_head timersDataReceived; exact (timersDataReceived_frame _).wp (Retained initial))
    | (index_material_head updateRxStats; exact (updateRxStats_frame _ _).wp (Retained initial))
    | (index_material_head dishonest; exact (dishonest_frame _).wp (Retained initial))
    | (index_material_head inetEcnDecapsulate; exact
        (frame_store (inetEcnDecapsulate_sameWGStore _ _ _)).wp (Retained initial))
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
    SameView view (Packets.rxFinish pid ready) := by
  rw [← RxCredits.rxFinishSource_eq]
  intro initial
  change Preserves (fun w => view w = initial) _
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

theorem afterConfirmation_retained (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    RetainsCall (ConsumeConfirmation.afterConfirmation pid pkt confirmed) := by
  apply retains_of_wp
  intro initial
  change Preserves (fun w => Retained initial (view w)) _
  unfold ConsumeConfirmation.afterConfirmation
  material_lower
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head timersHandshakeComplete; exact
        (timersHandshakeComplete_frame _ _).wp (Retained initial))
    | (index_material_head sendStagedPackets; exact retains_wp (sendStagedPackets_retained _) initial)
    | (index_material_head RxCredits.prepareRest; exact retains_wp (prepareRest_retained _ _) initial)
    | (index_material_head Packets.rxFinish; exact (rxFinish_frame _ _).wp (Retained initial))
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

end Leanux.Proofs.WG.Noise.PendingTickets
