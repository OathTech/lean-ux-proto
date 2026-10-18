import Leanux.Proofs.WG.AuthenticatedEffects.SendQueuePreservation
import Leanux.Proofs.WG.Queues.HandshakeSendResponse
import Leanux.Proofs.WG.Queues.HandshakeCookiePayment

/-! Actual receiver callbacks preserve the handshake-work queue except for
its observed keepalive/staging path. Existing holder and cookie frames supply
only their proved projections; no funding hypothesis is added here. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open Queues.RxCredits Queues.RxCredits.DurableHolders

private theorem holder_frame {action : WG.M α}
    (frame : ∀ initial, Leanux.Proofs.Framing.Preserves (Frame initial) action) : SameView queue action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have output := (hoare_iff_run_ambient _ _ _).mp (frame w) w a result v b (Frame.refl w) run
  exact congrArg (fun q => q.getD []) output.send

private theorem cookie_frame {action : WG.M α} (frame : SameCookie action) : SameView queue action :=
  frame.of_factor (fun s : WGOwnedView => (s.dev.map Device.sendWorkQueue).getD []) queue
    (fun _ => by simp only [queue,cookieView,cookieDevice,wgOwnedView,wgStoreView,Option.map_map,Function.comp_def])

private abbrev SendState := pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.State
private abbrev sendState := pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.view

private theorem send_state_frame {action : WG.M α} (frame : SameView sendState action) : SameView queue action :=
  frame.of_factor
    (fun s : Option SendState => (s.map (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.State.sendQueue)).getD [])
    queue (fun w => by
      change (w.dev.map Device.sendWorkQueue).getD [] =
        ((w.dev.map (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.state)).map
          (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.State.sendQueue)).getD []
      rw [Option.map_map]
      rfl)

theorem initiation_frame (msg : Key) : SameView queue (consumeInitiation msg) :=
  holder_frame (HandshakeLoans.consumeInitiation_frame msg)
theorem response_frame (msg : Key) : SameView queue (consumeResponse msg) :=
  holder_frame (HandshakeLoans.consumeResponse_frame msg)
theorem response_create_frame (pid : PeerId) : SameView queue (createResponse pid) :=
  holder_frame ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.create_frame) pid)
theorem mac_frame (pid : PeerId) (msg : Key) : SameView queue (addMacToPacket pid msg) :=
  holder_frame ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.addMacToPacket_frame) pid msg)
theorem send_frame (pid : PeerId) (msg : Key) : SameView queue (sendBufferToPeer pid msg) :=
  holder_frame ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.sendBufferToPeer_frame) pid msg)
theorem session_frame (pid : PeerId) : SameView queue (beginSession pid) :=
  (SessionCarrier.beginSession_view pid).of_factor (fun s => s.1.2.2.2.getD []) queue (fun _ => rfl)

theorem timer_arm_frame (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    SameView queue (armTimer pid timer delay caller) := by
  apply send_state_frame
  run_tac
    let theoremName := normalizePinnedName `_private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.armTimer_view
    let term := Lean.mkCIdent theoremName
    let p := Lean.mkIdent `pid
    let t := Lean.mkIdent `timer
    let d := Lean.mkIdent `delay
    let c := Lean.mkIdent `caller
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $term $p $t $d $c))
theorem timer_guard_frame (pid : PeerId) : SameView queue (modPeerTimerGuard pid) :=
  send_state_frame ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.modPeerTimerGuard_view) pid)
theorem timer_delete_frame (pid : PeerId) (timer : PeerTimer) : SameView queue (delTimer pid timer) :=
  send_state_frame ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.delTimer_view) pid timer)

theorem cookie_consume_frame (msg : Key) : SameView queue (cookieMessageConsume msg) := by
  apply holder_frame
  intro initial
  unfold cookieMessageConsume
  simp only [branch,hiddenClock64,invariant]
  repeat' first
    | (rx_retention_head indexLookup
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeLoans.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans.lookup_frame) _ _ initial)
    | (rx_retention_head peerPut; exact HolderWorkFrames.peerPut_frame _ initial)
    | holder_work_step initial

theorem load_frame : SameView queue Cookies.loadPhase :=
  Cookies.loadPhase_sameStore.of_factor (fun s : WGStoreView => (s.dev.map Device.sendWorkQueue).getD []) queue (fun _ => rfl)
theorem validate_frame (msg : Key) (src : SkbSource) (loaded : Bool) :
    SameView queue (cookieValidatePacket msg src loaded) :=
  cookie_frame (cookieValidatePacket_sameCookie msg src loaded)

private theorem send4_frame (e : Endpoint) (msg : Key) : SameView queue (send4 e none msg 0 false) :=
  holder_frame ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.send4_frame) e none msg 0 false)
private theorem send6_frame (e : Endpoint) (msg : Key) : SameView queue (send6 e none msg 0 false) :=
  holder_frame ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.send6_frame) e none msg 0 false)

theorem reply_frame (src : SkbSource) (msg : Key) : SameView queue (sendBufferAsReplyToSkb src msg) := by
  intro initial
  change Leanux.Proofs.Framing.Preserves (fun w => queue w = initial) _
  unfold sendBufferAsReplyToSkb endpointFromSkb
  simp only [branch,hiddenAlloc,invariant,unsupported]
  repeat' first
    | (rx_retention_head send4; exact (send4_frame _ _).wp (fun s => s = initial))
    | (rx_retention_head send6; exact (send6_frame _ _).wp (fun s => s = initial))
    | (rx_retention_head Functor.discard
       apply discard_view_spec queue (fun s => s = initial)
       change Leanux.Proofs.Framing.Preserves (fun w => queue w = initial) _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem cookie_send_frame (msg : Key) (src : SkbSource) : SameView queue (sendHandshakeCookie msg src) := by
  unfold sendHandshakeCookie
  exact (cookie_frame (cookieMessageCreate_sameCookie _ _ _)).bind (fun bytes => reply_frame src bytes)

macro "queue_callback_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head getPeer; exact (peer_read_frame _).wp (fun s => s = $initial))
  | (rx_retention_head setPeer; exact (peer_write_frame _ _).wp (fun s => s = $initial))
  | (rx_retention_head getDev; exact dev_read_frame.wp (fun s => s = $initial))
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi)
  | rx_retention_step)

theorem endpoint_frame (pid : PeerId) (src : SkbSource) : SameView queue (setPeerEndpointFromSkb pid src) := by
  intro initial
  change Leanux.Proofs.Framing.Preserves (fun w => queue w = initial) _
  unfold setPeerEndpointFromSkb setPeerEndpoint endpointFromSkb endpointEq dstCacheReset
  simp only [WG.andM,branch,invariant,unsupported,requireNotPending,hiddenJiffies,getAmbient]
  repeat' queue_callback_step initial

theorem complete_frame (pid : PeerId) : SameView queue (timersHandshakeComplete pid) := by
  intro initial
  change Leanux.Proofs.Framing.Preserves (fun w => queue w = initial) _
  unfold timersHandshakeComplete
  simp only [hidden]
  repeat' first
    | (rx_retention_head delTimer; exact (timer_delete_frame _ _).wp (fun s => s = initial))
    | queue_callback_step initial

end Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
