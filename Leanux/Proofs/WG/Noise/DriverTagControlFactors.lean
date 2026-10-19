import Leanux.WG.Device

/-! Native factors separated from observer and frame dependencies. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Control
open Leanux Leanux.WG
universe u

def stopPeerWith {m : Type → Type u} [Monad m]
    (required purge timers clear keys reset : PeerId → m Unit)
    (pid : PeerId) : m Unit := do
  required pid
  purge pid
  timers pid
  clear pid
  keys pid
  reset pid

def stopWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α)
    (peer : PeerId → m Unit) : m Unit := do
  for pid in (← lift getDev).peerList do
    _ ← lift (branch .stopPeersIter true)
    peer pid
  _ ← lift (branch .stopPeersIter false)
  if !(← lift getDev).handshakeQueue.empty then
    lift (unsupported "wg_stop with handshake messages queued for the receive worker (its timing)")
  _ ← lift (branch .stopDrainIter false)
  lift (modifyDev fun d => {d with handshakeQueueLen := 0})
  lift (socketReinit none none)

def downWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (stop : m Unit) : m Unit := do
  lift (modifyDev fun d => {d with running := false})
  stop

theorem stop_factor : WG.wgStop =
    stopWith (fun {_} a => a)
      (stopPeerWith (fun pid => requireNotPending pid "wg_stop while a handshake is queued")
        purgeStagedPackets timersStop handshakeClear keypairsClear resetLastSentHandshake) := by
  simp only [WG.wgStop, stopWith, stopPeerWith, bind_assoc]

theorem down_factor : WG.wgDown = downWith (fun {_} a => a) WG.wgStop := rfl

end Leanux.Proofs.WG.Noise.DriverTags.Control
