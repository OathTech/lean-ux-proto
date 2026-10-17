import Leanux.Proofs.WG.Config.PeerScalars
import Leanux.WG.Send

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config.QueuedFindings
open Leanux Leanux.WG

/-- A local state satisfying the legacy resident-peer domain. No reachability
claim is made; one old queued reference and one retained reference are present. -/
def pendingPeer : Peer := {
  remoteStatic := [], presharedKey := [], precomputedStaticStatic := [], internalId := 0,
  refcount := 2, handshakePending := true, lastSentHandshake := -5000000000 }
def pendingDevice : Device := {
  ifindex := 1, ifname := "wg0", numPeers := 1, peerList := [0],
  peers := ({} : Std.TreeMap PeerId Peer).insert 0 pendingPeer, sendWorkQueue := [0] }
def pendingState : WGWorld := {dev := some pendingDevice}
def queueRecord : HiddenRecord := {
  site := (HiddenSite.queued .sendWorker).info.id,
  bytes := 1 :: List.replicate 15 0 }
def supplied (ambient : Ambient) : Ambient := {ambient with
  armRecords := true,
  hidden := some [{site := HiddenSite.birthdateExpired.info.id, bytes := List.replicate 8 0}, queueRecord],
  unitPeers := [(1, Worker.sendWorker.index, 0)] }

/-- Exact copy of the pending legacy pure prediction, isolated because its
aggregate cannot build. No operational mirror is replaced by this expression. -/
def legacyQueuedDevice (d : Device) (pid : PeerId) (p : Peer) (now : Int64) : Device :=
  if !(p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now) || p.isDead then d
  else
    let acquired := withPeer d pid {p with refcount := p.refcount + 1}
    if p.handshakePending then
      withPeer acquired pid p
    else
      let pending := withPeer acquired pid {p with refcount := p.refcount + 1, handshakePending := true}
      {pending with sendWorkQueue := pending.sendWorkQueue ++ [pid]}

theorem pending_requeue_counterexample (ambient : Ambient) :
    pendingDevice.peers[0]? = some pendingPeer ∧
    ∃ final after,
      ((sendQueuedHandshakeInitiation 0 false).run pendingState).run (supplied ambient) =
        .ok (((), final), after) ∧
      final.dev.map Device.sendWorkQueue = some [0, 0] ∧
      (final.dev.bind (fun d => d.peers[0]?)).map Peer.refcount = some 3 ∧
      after.hidden = some [] ∧
      ∀ now, final.dev ≠ some (legacyQueuedDevice
        (withPeer pendingDevice 0 {pendingPeer with timerHandshakeAttempts := 0})
        0 {pendingPeer with timerHandshakeAttempts := 0} now) := by
  have observation :
      (((sendQueuedHandshakeInitiation 0 false).run pendingState).run (supplied ambient)).map
        (fun ((result, state), next) =>
          (result, state.dev.map Device.sendWorkQueue,
            (state.dev.bind (fun d => d.peers[0]?)).map Peer.refcount, next.hidden)) =
        .ok ((), some [0, 0], some 3, some []) := by rfl
  refine ⟨by simp [pendingDevice], ?_⟩
  cases run : ((sendQueuedHandshakeInitiation 0 false).run pendingState).run (supplied ambient) with
  | error stop => simp [run, Except.map] at observation
  | ok output =>
    obtain ⟨⟨result, final⟩, after⟩ := output
    cases result
    have parts : final.dev.map Device.sendWorkQueue = some [0, 0] ∧
        (final.dev.bind (fun d => d.peers[0]?)).map Peer.refcount = some 3 ∧
        after.hidden = some [] := by simpa [run, Except.map] using observation
    refine ⟨final, after, rfl, parts.1, parts.2.1, parts.2.2, ?_⟩
    intro now same
    have legacy : (legacyQueuedDevice
        (withPeer pendingDevice 0 {pendingPeer with timerHandshakeAttempts := 0})
        0 {pendingPeer with timerHandshakeAttempts := 0} now).sendWorkQueue = [0] := by
      unfold legacyQueuedDevice
      split <;> simp [withPeer, pendingDevice, pendingPeer]
    have mismatch := congrArg (fun dev => dev.map Device.sendWorkQueue) same
    rw [parts.1] at mismatch
    simp [legacy] at mismatch

end Leanux.Proofs.WG.Config.QueuedFindings
