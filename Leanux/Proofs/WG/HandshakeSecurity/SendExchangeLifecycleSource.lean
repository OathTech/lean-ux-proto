import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeRemovalSource
import Leanux.Proofs.WG.Queues.JointDelete

/-! Lifecycle shutdown and destruction expose every native handshake-work drain.
The native namespace pre-exit path has no such drain. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.SendExchange
open Leanux Leanux.WG Leanux.Proofs.Logged

def stopWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α) (drain : Option PeerId → m Unit) : m Unit := do
  for pid in (← step getDev).peerList do
    _ ← step (branch .stopPeersIter true)
    step (requireNotPending pid "wg_stop while a handshake is queued")
    step (purgeStagedPackets pid)
    timersStopWith step drain pid
    step (handshakeClear pid)
    step (keypairsClear pid)
    step (resetLastSentHandshake pid)
  _ ← step (branch .stopPeersIter false)
  if !(← step getDev).handshakeQueue.empty then
    step (unsupported "wg_stop with handshake messages queued for the receive worker (its timing)")
  _ ← step (branch .stopDrainIter false)
  step (modifyDev fun d => {d with handshakeQueueLen := 0})
  step (socketReinit none none)

def downWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α) (drain : Option PeerId → m Unit) : m Unit := do
  step (modifyDev fun d => {d with running := false})
  stopWith step drain

def destructWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α) (drain : Option PeerId → m Unit) : m Unit :=
  Configuration.destructWith step (removeAllWith step drain)
    (step (pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish))

def envDownWith {m : Type → Type} [Monad m]
    (step : {α : Type} → Leanux.M α → m α) (down : m Unit) : m Int := do
  let some d := (← step getWG).dev | return -ENODEV
  if !d.running then return 0
  step Env.requireIdleDevice
  down
  step (skipCut allocCuts)
  step Net.Fib.rtCacheFlush
  step (Net.Fib.netdevDown WG0_IFINDEX)
  step (modifyRouting fun w => {w with defaultRoute6 := false,addrs6 := [],ipv6Gen := w.ipv6Gen + 1})
  return 0

def envDeleteWith {m : Type → Type} [Monad m]
    (step : {α : Type} → Leanux.M α → m α) (down destruct : m Unit) : m Int :=
  Configuration.envDeleteWith step (step Env.requireIdleDevice) down destruct

theorem stop_factor : stopWith (fun {_} a => a) drainHandshakeSendWq = wgStop := rfl

theorem down_factor : downWith (fun {_} a => a) drainHandshakeSendWq = wgDown := rfl

theorem destruct_factor : destructWith (fun {_} a => a) drainHandshakeSendWq = wgDestruct := rfl

theorem envDown_factor : envDownWith (fun {_} a => a) (liftWG wgDown) = Env.wgDown := rfl

theorem envDelete_factor :
    envDeleteWith (fun {_} a => a) (liftWG wgDown) (liftWG wgDestruct) = Env.wgDelete :=
  Configuration.envDelete_factor.symm

end Leanux.Proofs.WG.HandshakeSecurity.SendExchange
