import Leanux.Proofs.WG.Lifetimes.ReceiveMaintenance

/-! A finite family of original receive-maintenance calls. The result type
retains the timer guards' Boolean results; no scheduler closure is implied. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged

inductive MaintenanceCall where
  | cache (pid : PeerId)
  | endpoint (pid : PeerId) (e : Endpoint)
  | arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64)
  | deleteTimer (pid : PeerId) (timer : PeerTimer)
  | guard (pid : PeerId)
  | modifyTimer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat)
  | handshakeComplete (pid : PeerId) (site : HiddenSite)
  | authenticatedReceived (pid : PeerId)
  | dataReceived (pid : PeerId)
  | traversal (pid : PeerId)
  | queuedHandshake (pid : PeerId) (retry : Bool)
  | keyFresh (pid : PeerId)

namespace MaintenanceCall

def Result : MaintenanceCall → Type
  | .guard _ | .modifyTimer _ _ _ _ => Bool
  | _ => Unit

def original (call : MaintenanceCall) : WG.M call.Result := match call with
  | .cache pid => dstCacheReset pid
  | .endpoint pid e => setPeerEndpoint pid e
  | .arm pid t d jc => armTimer pid t d jc
  | .deleteTimer pid t => delTimer pid t
  | .guard pid => modPeerTimerGuard pid
  | .modifyTimer site pid t d => modPeerTimer site pid t d
  | .handshakeComplete pid site => timersHandshakeComplete pid site
  | .authenticatedReceived pid => timersAnyAuthenticatedPacketReceived pid
  | .dataReceived pid => timersDataReceived pid
  | .traversal pid => timersTraversal pid
  | .queuedHandshake pid retry => sendQueuedHandshakeInitiation pid retry
  | .keyFresh pid => keepKeyFreshRx pid

def observed (call : MaintenanceCall) : MixedM call.Result := match call with
  | .cache pid => dstCacheResetMixed pid
  | .endpoint pid e => setPeerEndpointPrefix pid e
  | .arm pid t d jc => armTimerPrefix pid t d jc
  | .deleteTimer pid t => delTimerPrefix pid t
  | .guard pid => modPeerTimerGuardPrefix pid
  | .modifyTimer site pid t d => modPeerTimerPrefix site pid t d
  | .handshakeComplete pid site => timersHandshakeCompletePrefix pid site
  | .authenticatedReceived pid => timersAnyAuthenticatedPacketReceivedPrefix pid
  | .dataReceived pid => timersDataReceivedPrefix pid
  | .traversal pid => timersTraversalPrefix pid
  | .queuedHandshake pid retry => sendQueuedHandshakeInitiationPrefix pid retry
  | .keyFresh pid => keepKeyFreshRxPrefix pid

theorem erases (call : MaintenanceCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | cache pid => exact dstCacheResetMixed_erases pid
  | endpoint pid e => exact setPeerEndpointPrefix_erases pid e
  | arm pid t d jc => exact armTimerPrefix_erases pid t d jc
  | deleteTimer pid t => exact delTimerPrefix_erases pid t
  | guard pid => exact modPeerTimerGuardPrefix_erases pid
  | modifyTimer site pid t d => exact modPeerTimerPrefix_erases site pid t d
  | handshakeComplete pid site => exact timersHandshakeCompletePrefix_erases pid site
  | authenticatedReceived pid => exact timersAnyAuthenticatedPacketReceivedPrefix_erases pid
  | dataReceived pid => exact timersDataReceivedPrefix_erases pid
  | traversal pid => exact timersTraversalPrefix_erases pid
  | queuedHandshake pid retry => exact sendQueuedHandshakeInitiationPrefix_erases pid retry
  | keyFresh pid => exact keepKeyFreshRxPrefix_erases pid

theorem preserves_ambient (c : AmbientContracts I)
    (hq : ∀ pid, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})))
    (call : MaintenanceCall) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call with
  | cache pid => exact AmbientContracts.drop (dstCacheResetMixed_spec c (fun _ => True) pid)
  | endpoint pid e => exact AmbientContracts.drop (setPeerEndpointPrefix_spec c (fun _ => True) pid e)
  | arm pid t d jc => exact AmbientContracts.drop (armTimerPrefix_spec c (fun _ => True) pid t d jc)
  | deleteTimer pid t => exact AmbientContracts.drop (delTimerPrefix_spec c (fun _ => True) pid t)
  | guard pid => exact AmbientContracts.drop (modPeerTimerGuardPrefix_spec c (fun _ => True) pid)
  | modifyTimer site pid t d => exact AmbientContracts.drop (modPeerTimerPrefix_spec c (fun _ => True) site pid t d)
  | handshakeComplete pid site => exact AmbientContracts.drop (timersHandshakeCompletePrefix_spec c (fun _ => True) pid site)
  | authenticatedReceived pid => exact AmbientContracts.drop (timersAnyAuthenticatedPacketReceivedPrefix_spec c (fun _ => True) pid)
  | dataReceived pid => exact AmbientContracts.drop (timersDataReceivedPrefix_spec c (fun _ => True) pid)
  | traversal pid => exact AmbientContracts.drop (timersTraversalPrefix_spec c (fun _ => True) pid)
  | queuedHandshake pid retry => exact sendQueuedHandshakeInitiationPrefix_preserves_ambient c hq pid retry
  | keyFresh pid => exact keepKeyFreshRxPrefix_preserves_ambient c hq pid

theorem preserves_product (c : ProductAmbientContracts I)
    (hq : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}))))
    (call : MaintenanceCall) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  cases call with
  | cache pid => exact ProductAmbientContracts.drop (dstCacheResetMixed_spec_product c (fun _ => True) pid)
  | endpoint pid e => exact ProductAmbientContracts.drop (setPeerEndpointPrefix_spec_product c (fun _ => True) pid e)
  | arm pid t d jc => exact ProductAmbientContracts.drop (armTimerPrefix_spec_product c (fun _ => True) pid t d jc)
  | deleteTimer pid t => exact ProductAmbientContracts.drop (delTimerPrefix_spec_product c (fun _ => True) pid t)
  | guard pid => exact ProductAmbientContracts.drop (modPeerTimerGuardPrefix_spec_product c (fun _ => True) pid)
  | modifyTimer site pid t d => exact ProductAmbientContracts.drop (modPeerTimerPrefix_spec_product c (fun _ => True) site pid t d)
  | handshakeComplete pid site => exact ProductAmbientContracts.drop (timersHandshakeCompletePrefix_spec_product c (fun _ => True) pid site)
  | authenticatedReceived pid => exact ProductAmbientContracts.drop (timersAnyAuthenticatedPacketReceivedPrefix_spec_product c (fun _ => True) pid)
  | dataReceived pid => exact ProductAmbientContracts.drop (timersDataReceivedPrefix_spec_product c (fun _ => True) pid)
  | traversal pid => exact ProductAmbientContracts.drop (timersTraversalPrefix_spec_product c (fun _ => True) pid)
  | queuedHandshake pid retry => exact sendQueuedHandshakeInitiationPrefix_preserves_product c hq pid retry
  | keyFresh pid => exact keepKeyFreshRxPrefix_preserves_product c hq pid

theorem allocation (call : MaintenanceCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient sendWorkQueue_allocation

end MaintenanceCall

/-- Clock failure retains the four actual accesses. The expiry-only setup
premises remain valid inputs; the observed deletion additionally clears the
wheel slot, which does not change either access stamp or the Ambient clock. -/
theorem timersHandshakeCompletePrefix_clock_failure (pid : PeerId) (site : HiddenSite)
    (w afterDelete clockEntry : WGWorld) (ambient : Ambient)
    (p q : Peer) (h : List LifetimeEvent) (e : Stop)
    (hp : ((getPeer pid).run w).run ambient = .ok ((p, w), ambient))
    (hdel : ((setPeer pid (p.setTimer .retransmitHandshake none)).run w).run ambient = .ok (((), afterDelete), ambient))
    (hq : ((getPeer pid).run afterDelete).run ambient = .ok ((q, afterDelete), ambient))
    (hreset : ((setPeer pid {q with timerHandshakeAttempts := 0, sentLastminuteHandshake := false}).run afterDelete).run ambient = .ok (((), clockEntry), ambient))
    (hclock : (((hidden site : WG.M (List UInt8))).run clockEntry).run ambient = .error e) :
    runStatePrefix (timersHandshakeCompletePrefix pid site) w ambient h =
      (.error e, h ++ [.peer (.read pid p.internalId), .peer (.write pid p.internalId),
        .peer (.read pid q.internalId), .peer (.write pid q.internalId)]) := by
  cases hd : w.dev with
  | none =>
    simp [getPeer, getDev, hd, invariant, AmbientM.invariant] at hp
    cases hp
  | some d =>
    cases he : d.peers[pid]? with
    | none =>
      simp [getPeer, getDev, hd, he, invariant, AmbientM.invariant] at hp
      cases hp
    | some actual =>
      have hp' : ((getPeer pid).run w).run ambient = .ok ((actual, w), ambient) := by
        simp [getPeer, getDev, hd, he]
      rw [hp'] at hp
      cases hp
      simp [setPeer, modifyDev, hd] at hdel
      subst afterDelete
      simp [getPeer, getDev] at hq
      subst q
      have hc : (AmbientM.hidden site).run ambient = .error e := by
        cases hx : (AmbientM.hidden site).run ambient with
        | error stop => simpa [hidden, hx] using hclock
        | ok value => simp [hidden, hx] at hclock
      simp [timersHandshakeCompletePrefix, delTimerPrefix, modifyPeerKeysPrefix,
        runStatePrefix_bind, getPeerMixed_run, setPeerMixed_run, liftWGPrefix, runStatePrefix_lift,
        getPeer, getDev, setPeer, modifyDev, hd, he, hidden, hc,
        Peer.setTimer, Peer.setWheel, List.append_assoc]

end Leanux.Proofs.WG.Lifetimes
