import Leanux.Proofs.WG.HandshakeSecurity.ExchangeSourceFrames
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDriverSource

/-! Exchange-ledger transport through actual queued initiation creation. The
native H1 source frames remain explicit, and every later Stop retains completed
creator receipts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

open Lean Meta Elab Tactic in
elab "exchange_update_cut" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StatePrefixPreserves || target.isAppOf ``StatePrefixEnsures do
    throwError "not a state-prefix contract"
  let args := target.getAppArgs
  let action := if target.isAppOf ``StatePrefixPreserves then args.back! else args[args.size - 2]!
  let action := action.consumeMData.headBeta
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let first := action.getAppArgs[action.getAppArgs.size - 2]!.consumeMData
  unless first.isAppOf ``liftWGPrefix do throwError "not a lifted getter"
  unless first.getAppArgs.back!.consumeMData.isAppOf ``getPeer do throwError "not the peer getter"
  let .lam _ _ body _ := action.getAppArgs.back!.consumeMData | throwError "not a direct getter continuation"
  let body := body.consumeMData.headBeta
  unless body.isAppOf ``Bind.bind do throwError "not a subsequent write"
  let write := body.getAppArgs[body.getAppArgs.size - 2]!.consumeMData
  unless write.isAppOf ``liftWGPrefix do throwError "not a lifted write"
  unless write.getAppArgs.back!.consumeMData.isAppOf ``setPeer do throwError "not a peer write"

macro "exchange_send_step " h:term : tactic => `(tactic| first
  | unfold Preserves
  | (nonce_source_head getPeer; exact lift _ (read_peer _))
  | (nonce_source_head branchExpired; exact lift _ (fun history => frame_world history _ (branchExpired_sameWGWorld _ _ _ _)))
  | (nonce_source_head addMacToPacket; exact lift_tag _ (H1HandshakeTagFrames.mac $h _ _))
  | (nonce_source_head timersTraversal; exact lift_tag _ (H1HandshakeTagFrames.traversal $h _))
  | (nonce_source_head timersAnyAuthenticatedPacketSent; exact lift_tag _ (H1HandshakeTagFrames.deleteTimer $h _ _))
  | (nonce_source_head timersHandshakeInitiated; exact lift_tag _ (H1HandshakeTagFrames.initiated $h _))
  | (nonce_source_head sendBufferToPeer; exact lift_tag _ (H1HandshakeTagFrames.send $h _ _))
  | (first | nonce_source_head branch | nonce_source_head hiddenClock64 | nonce_source_head hidden | nonce_source_head invariant
     exact ambient _)
  | (exchange_update_cut; apply update_bind; first | intro p; rfl | intro u)
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | (nonce_source_head Pure.pure; exact pure _)
  | (nonce_source_head ite; apply conditional)
  | split
  | (with_reducible intro x; try dsimp only))

theorem send_checked (H1 : H1ExchangeEdges) (frames : H1HandshakeTagFrames) (pid : PeerId) :
    Preserves (SendExchange.sendWith ExchangeDriver.sendOps pid) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) Safe _
  unfold SendExchange.sendWith
  simp only [ExchangeDriver.sendOps]
  repeat' first
    | (nonce_source_head Exchange.createInitiation; exact createInitiation_checked H1 _)
    | exchange_send_step frames

theorem worker_checked (H1 : H1ExchangeEdges) (frames : H1HandshakeTagFrames) (pid : PeerId) :
    Preserves (SendExchange.workerWith ExchangeDriver.sendOps pid) := by
  unfold SendExchange.workerWith
  exact StatePrefixEnsures.bind (send_checked H1 frames pid)
    (fun _ => lift _ (peer_put _))

theorem afterTake_checked (H1 : H1ExchangeEdges) (frames : H1HandshakeTagFrames) (pid : PeerId) :
    Preserves (SendExchange.afterTakeWith (fun {_} action => liftWGPrefix action)
      (SendExchange.workerWith ExchangeDriver.sendOps) pid) := by
  unfold SendExchange.afterTakeWith
  apply StatePrefixEnsures.bind (read_saved pid)
  intro p
  dsimp only
  split
  · apply StatePrefixEnsures.bind (saved_ambient _ _ _)
    intro _
    apply StatePrefixEnsures.bind (saved_tag pid p getDev (getDev_sameWGStore.of_factor
      (fun s : WGStoreView => fun target => (s.dev.bind fun d => d.peers[target]?).map Peer.handshakeState)
      handshakeTagAt (fun _ => rfl)))
    intro d
    apply StatePrefixEnsures.bind (write_saved pid p
      (fun q => {q with handshakePending := d.sendWorkQueue.contains pid}) rfl)
    intro _
    repeat' first
      | (nonce_source_head SendExchange.workerWith; exact worker_checked H1 frames pid)
      | exchange_send_step frames
  · apply StatePrefixEnsures.bind (saved_tag pid p getDev (getDev_sameWGStore.of_factor
      (fun s : WGStoreView => fun target => (s.dev.bind fun d => d.peers[target]?).map Peer.handshakeState)
      handshakeTagAt (fun _ => rfl)))
    intro d
    apply StatePrefixEnsures.bind (write_saved pid p
      (fun q => {q with handshakePending := d.sendWorkQueue.contains pid}) rfl)
    intro _
    repeat' first
      | (nonce_source_head SendExchange.workerWith; exact worker_checked H1 frames pid)
      | (nonce_source_head hidden; exact ambient _)
      | exchange_send_step frames

theorem flushed_checked (H1 : H1ExchangeEdges) (frames : H1HandshakeTagFrames) (pid : PeerId) :
    Preserves (ExchangeDriver.flushed pid) := by
  unfold ExchangeDriver.flushed SendExchange.flushedWith
  exact StatePrefixEnsures.bind (lift _ (modify_device _ (fun _ => rfl)))
    (fun _ => afterTake_checked H1 frames pid)

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
