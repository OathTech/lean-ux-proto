import Leanux.Proofs.WG.Lifetimes.ReceiveMaintenance

/-! A finite family of original receive-maintenance calls. The result type
retains the timer guards' Boolean results; no scheduler closure is implied. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged

inductive MaintenanceCall where
  | cache (pid : PeerId)
  | endpoint (pid : PeerId) (e : Endpoint)
  | arm (pid : PeerId) (timer : PeerTimer) (delay : Nat)
  | deleteTimer (pid : PeerId) (timer : PeerTimer)
  | guard (pid : PeerId)
  | modifyTimer (pid : PeerId) (timer : PeerTimer) (delay : Nat)
  | handshakeComplete (pid : PeerId) (site : HiddenSite)
  | authenticatedReceived (pid : PeerId)
  | dataReceived (pid : PeerId)
  | traversal (pid : PeerId)
  | queuedHandshake (pid : PeerId) (retry : Bool)
  | keyFresh (pid : PeerId)

namespace MaintenanceCall

def Result : MaintenanceCall → Type
  | .guard _ | .modifyTimer _ _ _ => Bool
  | _ => Unit

def original (call : MaintenanceCall) : M call.Result := match call with
  | .cache pid => dstCacheReset pid
  | .endpoint pid e => setPeerEndpoint pid e
  | .arm pid t d => armTimer pid t d
  | .deleteTimer pid t => delTimer pid t
  | .guard pid => modPeerTimerGuard pid
  | .modifyTimer pid t d => modPeerTimer pid t d
  | .handshakeComplete pid site => timersHandshakeComplete pid site
  | .authenticatedReceived pid => timersAnyAuthenticatedPacketReceived pid
  | .dataReceived pid => timersDataReceived pid
  | .traversal pid => timersTraversal pid
  | .queuedHandshake pid retry => sendQueuedHandshakeInitiation pid retry
  | .keyFresh pid => keepKeyFreshRx pid

def observed (call : MaintenanceCall) : MixedM call.Result := match call with
  | .cache pid => dstCacheResetMixed pid
  | .endpoint pid e => setPeerEndpointPrefix pid e
  | .arm pid t d => armTimerPrefix pid t d
  | .deleteTimer pid t => delTimerPrefix pid t
  | .guard pid => modPeerTimerGuardPrefix pid
  | .modifyTimer pid t d => modPeerTimerPrefix pid t d
  | .handshakeComplete pid site => timersHandshakeCompletePrefix pid site
  | .authenticatedReceived pid => timersAnyAuthenticatedPacketReceivedPrefix pid
  | .dataReceived pid => timersDataReceivedPrefix pid
  | .traversal pid => timersTraversalPrefix pid
  | .queuedHandshake pid retry => sendQueuedHandshakeInitiationPrefix pid retry
  | .keyFresh pid => keepKeyFreshRxPrefix pid

theorem erases (call : MaintenanceCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | cache pid => exact dstCacheResetMixed_erases pid
  | endpoint pid e => exact setPeerEndpointPrefix_erases pid e
  | arm pid t d => exact armTimerPrefix_erases pid t d
  | deleteTimer pid t => exact delTimerPrefix_erases pid t
  | guard pid => exact modPeerTimerGuardPrefix_erases pid
  | modifyTimer pid t d => exact modPeerTimerPrefix_erases pid t d
  | handshakeComplete pid site => exact timersHandshakeCompletePrefix_erases pid site
  | authenticatedReceived pid => exact timersAnyAuthenticatedPacketReceivedPrefix_erases pid
  | dataReceived pid => exact timersDataReceivedPrefix_erases pid
  | traversal pid => exact timersTraversalPrefix_erases pid
  | queuedHandshake pid retry => exact sendQueuedHandshakeInitiationPrefix_erases pid retry
  | keyFresh pid => exact keepKeyFreshRxPrefix_erases pid

theorem preserves_ambient (c : AmbientContracts I)
    (hq : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})))
    (call : MaintenanceCall) : PrefixPreserves I LifetimeEvent.Safe call.observed := by
  cases call with
  | cache pid => exact AmbientContracts.drop (dstCacheResetMixed_spec c (fun _ => True) pid)
  | endpoint pid e => exact AmbientContracts.drop (setPeerEndpointPrefix_spec c (fun _ => True) pid e)
  | arm pid t d => exact AmbientContracts.drop (armTimerPrefix_spec c (fun _ => True) pid t d)
  | deleteTimer pid t => exact AmbientContracts.drop (delTimerPrefix_spec c (fun _ => True) pid t)
  | guard pid => exact AmbientContracts.drop (modPeerTimerGuardPrefix_spec c (fun _ => True) pid)
  | modifyTimer pid t d => exact AmbientContracts.drop (modPeerTimerPrefix_spec c (fun _ => True) pid t d)
  | handshakeComplete pid site => exact AmbientContracts.drop (timersHandshakeCompletePrefix_spec c (fun _ => True) pid site)
  | authenticatedReceived pid => exact AmbientContracts.drop (timersAnyAuthenticatedPacketReceivedPrefix_spec c (fun _ => True) pid)
  | dataReceived pid => exact AmbientContracts.drop (timersDataReceivedPrefix_spec c (fun _ => True) pid)
  | traversal pid => exact AmbientContracts.drop (timersTraversalPrefix_spec c (fun _ => True) pid)
  | queuedHandshake pid retry => exact sendQueuedHandshakeInitiationPrefix_preserves_ambient c hq pid retry
  | keyFresh pid => exact keepKeyFreshRxPrefix_preserves_ambient c hq pid

theorem allocation (call : MaintenanceCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient sendWorkQueue_allocation

end MaintenanceCall

/-- The handshake-completion clock failure follows two actual peer updates.
Its four-event prefix is specified using consecutive original executions. -/
theorem timersHandshakeCompletePrefix_clock_failure (pid : PeerId) (site : HiddenSite)
    (w afterDelete clockEntry : World) (p q : Peer) (h : List LifetimeEvent) (e : Stop)
    (hp : (getPeer pid).run w = .ok (p, w))
    (hdel : (setPeer pid (p.setTimer .retransmitHandshake none)).run w = .ok ((), afterDelete))
    (hq : (getPeer pid).run afterDelete = .ok (q, afterDelete))
    (hreset : (setPeer pid {q with timerHandshakeAttempts := 0, sentLastminuteHandshake := false}).run afterDelete = .ok ((), clockEntry))
    (hclock : (hidden site).run clockEntry = .error e) :
    runPrefix (timersHandshakeCompletePrefix pid site) w h =
      (.error e, h ++ [.peer (.read pid p.internalId), .peer (.write pid p.internalId),
        .peer (.read pid q.internalId), .peer (.write pid q.internalId)]) := by
  have hw : w.k.wg.isSome = true := by
    cases hd : w.k.wg with
    | none => simp [getPeer, getDev, getK, hd, invariant] at hp
    | some d => rfl
  have hd : afterDelete.k.wg.isSome = true := by
    cases he : afterDelete.k.wg with
    | none => simp [getPeer, getDev, getK, he, invariant] at hq
    | some d => rfl
  simp only [timersHandshakeCompletePrefix, delTimerPrefix, modifyPeerKeysPrefix,
    runPrefix_bind, getPeerMixed_run, hp, hq, setPeerMixed_run, hw, hd,
    ↓reduceIte, hdel, hreset, runPrefix_lift, hclock]
  simp [Peer.setTimer, List.append_assoc]

end Leanux.Proofs.WG.Lifetimes
