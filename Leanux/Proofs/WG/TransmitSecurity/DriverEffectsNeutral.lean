import Leanux.Proofs.WG.TransmitSecurity.DriverSource
import Leanux.Proofs.WG.AuthenticatedEffects.PacketEffectsFrames

/-! Exact neutral effect specializations. They retain native guards, returns,
Stops and journals, so existing concrete carriers need no extra assumptions. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects TimerEffects
variable (hooks : Hooks E)

theorem noKey_lift (neutral : effectOps hooks = lifted) (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    PacketEffects.noKeyWith (effectOps hooks) pid packets keypair invalid =
      liftWGPrefix (Lifetimes.stagedOutNokey pid packets keypair invalid) := by
  rw [neutral,PacketEffects.noKey_lifted]

theorem prepare_lift (neutral : effectOps hooks = lifted) (pid : PeerId) (pkt : RxPacket) :
    PacketEffects.prepareWith (effectOps hooks) pid pkt = liftWGPrefix (Queues.RxCredits.prepareRest pid pkt) := by
  rw [neutral,PacketEffects.prepare_lifted]

theorem expiredKeepalive_lift (neutral : effectOps hooks = lifted) (pid : PeerId) :
    expiredKeepaliveObserved hooks pid = (do
      keepaliveObserved hooks pid
      if ← liftWGPrefix (branch .keepaliveNeedAnother (← liftWGPrefix (getPeer pid)).timerNeedAnotherKeepalive) then
        liftWGPrefix (setPeer pid { (← liftWGPrefix (getPeer pid)) with timerNeedAnotherKeepalive := false })
        liftWGPrefix (discard <| modPeerTimer .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS)) := by
  unfold expiredKeepaliveObserved
  rw [neutral,expiredKeepalive_lifted]

theorem persistent_lift (pid : PeerId) :
    persistentObserved hooks pid = (do
      if ← liftWGPrefix (branch .persistentKeepaliveInterval ((← liftWGPrefix (getPeer pid)).persistentKeepaliveInterval != 0)) then
        keepaliveObserved hooks pid) := rfl

theorem timer_retransmit_lift (neutral : effectOps hooks = lifted)
    (release : hooks.peerRelease = fun peer => liftWGPrefix (peerPut peer))
    (purge : hooks.stagedPurge = fun pid => liftWGPrefix (purgeStagedPackets pid)) (pid : PeerId) :
    timerObserved hooks pid .retransmitHandshake = liftWGPrefix (expiredRetransmitHandshake pid) := by
  change HandshakeSecurity.StagedDisposal.Effects.retransmitWith (effectOps hooks) hooks.peerRelease hooks.stagedPurge pid = _
  rw [neutral,release,purge]
  exact (HandshakeSecurity.StagedDisposal.Effects.retransmit_neutral lifted pid).trans
    (retransmit_lifted pid)

theorem timer_new_lift (neutral : effectOps hooks = lifted)
    (release : hooks.peerRelease = fun peer => liftWGPrefix (peerPut peer)) (pid : PeerId) :
    timerObserved hooks pid .newHandshake = liftWGPrefix (expiredNewHandshake pid) := by
  change HandshakeSecurity.StagedDisposal.Effects.newHandshakeWith (effectOps hooks) hooks.peerRelease pid = _
  rw [neutral,release]
  exact (HandshakeSecurity.StagedDisposal.Effects.newHandshake_neutral lifted pid).trans
    (expiredNew_lifted pid)

end Leanux.Proofs.WG.TransmitSecurity.Driver
