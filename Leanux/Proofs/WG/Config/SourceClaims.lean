import Leanux.Proofs.WG.Config.StructuralSourceClaims
import Leanux.Proofs.WG.Config.PortSourceClaims
import Leanux.Proofs.WG.Config.IdentitySourceClaims
import Leanux.Proofs.WG.Config.LeafSourceClaims
import Leanux.Proofs.WG.Config.QuietRemoval
import Leanux.Proofs.WG.Config.PeerDead
import Leanux.Proofs.WG.Config.AllowedOwnerClear
import Leanux.Proofs.WG.Config.AllowedGeneralReplacement
import Leanux.Proofs.WG.Config.Identity
import Leanux.Proofs.WG.Config.Port
import Leanux.Proofs.WG.Config.RoundTrip
import Leanux.Proofs.WG.Config.DeviceScalars
import Leanux.Proofs.WG.Config.RoundTripReturns
import Leanux.Proofs.WG.Config.Fwmark
import Leanux.Proofs.WG.Config.ClearedSources
import Leanux.Proofs.WG.Config.SocketPorts
import Leanux.Proofs.WG.Config.FwmarkEffects
import Leanux.Proofs.WG.Config.DevicePorts
import Leanux.Proofs.WG.Config.RandomPort
import Leanux.Proofs.WG.Config.ZeroPort
import Leanux.Proofs.WG.Config.RecordedPort
import Leanux.Proofs.WG.Config.ExpiryEffects
import Leanux.Proofs.WG.Config.ExpiryClock
import Leanux.Proofs.WG.Config.KeyInstall
import Leanux.Proofs.WG.Config.KeyInstallEffects
import Leanux.Proofs.WG.Config.DumpCancellation
import Leanux.Proofs.WG.Config.KeyRequest
import Leanux.Proofs.WG.Config.Getter
import Leanux.Proofs.WG.Config.ScalarGetter

import Leanux.Proofs.WG.Config.ConcreteFrames

/-! Concrete source-level contracts. Public WG projections live in Statements. -/
namespace Leanux.Proofs.WG.Config.SourceClaims
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Every successful lifted expiry exposes the actual Product prefix and
clock states, preserving all original fixture observations. -/
theorem original_expiry_clock_relation (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (w v : World) (device : w.wg.dev = some d)
    (run : (liftWG (expireCurrentPeerKeypairs pid)).run w = .ok ((), v)) :
    ∃ now before after,
      (liftWG (expiryReadPrefix pid)).run w = .ok ((), before) ∧
      (liftWG (hiddenClock64 .resetLastSent : WG.M Int64)).run before = .ok (now, after) ∧
      v.wg.dev = some (expiredDevice d pid p now) := by
  change (((expireCurrentPeerKeypairs pid).run w.wg).run w.ambient >>= _) = _ at run
  cases executed : ((expireCurrentPeerKeypairs pid).run w.wg).run w.ambient with
  | error stop => rw [executed] at run; cases run
  | ok pair =>
    obtain ⟨⟨value, final⟩, inputs⟩ := pair
    rw [executed] at run
    cases run
    obtain ⟨now, before, beforeAmbient, after, afterAmbient, prefixRun, read, effect⟩ :=
      expireCurrent_clock pid d p resident w.wg final w.ambient inputs device executed
    refine ⟨now, {w with wg := before, ambient := beforeAmbient},
      {w with wg := after, ambient := afterAmbient}, ?_, ?_, effect⟩
    · change (((expiryReadPrefix pid).run w.wg).run w.ambient >>= _) = _
      rw [prefixRun]; rfl
    · change (((hiddenClock64 .resetLastSent : WG.M Int64).run before).run beforeAmbient >>= _) = _
      rw [read]; rfl

/-- The corrected queue effect follows the actual dispatch observation after
the age-test read. Product prefix/clock states and every original premise remain. -/
theorem original_queued_handshake_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (w v : World) (device : w.wg.dev = some d)
    (run : (liftWG (sendQueuedHandshakeInitiation pid false)).run w = .ok ((), v)) :
    ∃ now seen before after,
      (liftWG (queuedReadPrefix pid)).run w =
        .ok ({p with timerHandshakeAttempts := 0}, before) ∧
      (liftWG (hiddenClock64 .birthdateExpired : WG.M Int64)).run before = .ok (now, after) ∧
      (liftWG (observedQueuedAfterClock pid {p with timerHandshakeAttempts := 0} now)).run after =
        .ok (seen, v) ∧
      match seen with
      | none => v.wg.dev = some (withPeer d pid {p with timerHandshakeAttempts := 0}) ∧
          (¬p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now ∨ p.isDead = true)
      | some queued => p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now ∧
          p.isDead = false ∧ v.wg.dev = some (queuedDeviceAfterInspection
            (withPeer d pid {p with timerHandshakeAttempts := 0}) pid {p with timerHandshakeAttempts := 0} now queued) := by
  change (((sendQueuedHandshakeInitiation pid false).run w.wg).run w.ambient >>= _) = _ at run
  cases executed : ((sendQueuedHandshakeInitiation pid false).run w.wg).run w.ambient with
  | error stop => rw [executed] at run; cases run
  | ok pair =>
    obtain ⟨⟨value, final⟩, inputs⟩ := pair
    rw [executed] at run
    cases run
    obtain ⟨now, seen, before, beforeAmbient, after, afterAmbient, prefixRun, read, observed, effect⟩ :=
      sendQueued_clock pid d p resident w.wg final w.ambient inputs device executed
    refine ⟨now, seen, {w with wg := before, ambient := beforeAmbient},
      {w with wg := after, ambient := afterAmbient}, ?_, ?_, ?_, effect⟩
    · change (((queuedReadPrefix pid).run w.wg).run w.ambient >>= _) = _
      rw [prefixRun]; rfl
    · change (((hiddenClock64 .birthdateExpired : WG.M Int64).run before).run beforeAmbient >>= _) = _
      rw [read]; rfl
    · change (((observedQueuedAfterClock pid {p with timerHandshakeAttempts := 0} now).run after).run afterAmbient >>= _) = _
      rw [observed]; rfl

/-- Corrected staged fallback uses the actual queue inspection, on the original invalid-key domain. -/
theorem original_staged_invalid_key (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (invalid : ∀ id k, p.keypairCurrent = some id → d.keypairs[id]? = some k → k.sending.isValid = false) :
    Campaign2.Ensures (observedInvalidStaged pid) (fun s => s.wg.device = some d)
      (invalidStagedObservation d pid p) :=
  staged_invalid pid d p resident invalid

/-- Corrected peer effects include the actual staged-send observation. -/
theorem original_key_peer_effects (pid : PeerId) (d : Device) (p : Peer) (sendStaged : Bool)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (observedKeyPeerSource pid sendStaged) (fun s => s.wg.device = some d)
      (keyPeerObservation d pid p sendStaged) :=
  keyPeer_complete pid d p sendStaged resident

/-- Corrected ordered peer effects retain duplicates and actual intermediate observations. -/
theorem original_key_peer_loop_effects (pids : List PeerId) (d : Device) (sendStaged : Bool) :
    Campaign2.Ensures (observedKeyPeerLoopSource pids sendStaged)
      (fun s => s.wg.device = some d)
      (fun observations s => ∃ final, s.wg.device = some final ∧
        ObservedKeyPeerRun sendStaged d pids observations final) :=
  keyPeerLoop_complete pids d sendStaged

/-- Corrected installation effects follow actual peer observations after key publication. -/
theorem original_key_install_effects (d : Device) (key : Key) :
    Campaign2.Ensures (observedKeyInstallSource key) (fun s => s.wg.device = some d)
      (fun observations s => ∃ final, s.wg.device = some final ∧
        ObservedKeyPeerRun (requestsStagedSend d key) (installedDevice d key) d.peerList observations final) :=
  keyInstall_complete d key

/-- The unchanged no-collision domain has the corrected observed installation effect. -/
theorem original_private_key_request_no_collision (d : Device) (key : Key)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key) :
    Campaign2.Ensures (wgSetDevice (privateKeyAttrs d key))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d)
      (fun ret s => ret = 0 ∧ ∃ final observations, s.wg.device = some final ∧
        ObservedKeyPeerRun (requestsStagedSend d key)
          (installedDevice (requestGeneration d) key) d.peerList observations final) :=
  setDevice_private_changed_no_collision d key changed absent

/-- The original bounded single-peer callback returns its exact dump and device. -/
theorem original_single_peer_dump_callback (pid : PeerId) (d : Device) (p : Peer)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (empty : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE) :
    Returns (wgGetDeviceDump { hasWg := true } 0 {}) (fun w => w.dev = some d)
      (fun result w => result = singlePeerDump d p ∧ w.dev = some d) :=
  wgGetDeviceDump_single pid d p peers resident empty room

/-- The original one-chunk getter returns canonical JSON and its drained socket. -/
theorem original_single_peer_getter (pid : PeerId) (d : Device) (p : Peer) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (noIps : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Returns (wgGetDevice (byIndex d))
      (fun w => w.dev = some d ∧ w.nlSock7 = sock ∧ selectsDevice w d)
      (fun result w => result = .ok (singlePeerJson d p) ∧ w.dev = some d ∧
        w.nlSock7 = { completedSock sock d p with queue := [] }) :=
  wgGetDevice_single pid d p sock peers resident noIps room idle empty

/-- Scalar set/get retains exact applied configuration, including a later malformed peer. -/
theorem original_scalar_get_after_set (d : Device) (key psk : Key) (interval : Nat) (bad : Bool)
    (pid : PeerId) (p : Peer) (sock : NlSock)
    (peers : d.peerList = [pid])
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (noIps : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Returns (do
      let ret ← wgSetDevice (scalarDeviceAttrs d key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun w => w.wg.device = some d ∧ w.wg.nlSock7 = sock ∧ ClaimView.selectsDevice w d)
      (fun result w =>
        let updated := scalarRequestDevice d pid p psk interval
        let configured := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        result = ((if bad then -EINVAL else 0), .ok (singlePeerJson updated configured)) ∧ w.wg.device = some updated ∧
          w.wg.nlSock7 = { completedSock sock updated configured with queue := [] }) :=
  scalar_outer_get_after_set d key psk interval bad pid p sock peers found resident live bounded down noIps room idle empty

/-- Replacing a stopped peer's singleton root-leaf allowed-IP list with an
empty list removes the node, clears its family root, increments the trie
sequence, and removes that node from every peer list. The public device
setter increments its generation and balances the lookup reference. -/
theorem original_allowedips_replace_single_root (v4 : Bool) (key : Key) (pid : PeerId)
    (d : Device) (p : Peer) (id : NodeId) (n : AipNode)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (peer : d.peers[pid]? = some p) (listed : p.allowedipsList = [id])
    (resident : d.nodes[id]? = some n) (leaf : n.bit = #[none, none])
    (parent : n.parent = rootSlot v4) (_owned : n.peer = some pid)
    (_root : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = some id)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Returns (wgSetDevice (replaceAllowedipsDeviceAttrs d key))
      (fun w => w.dev = some d ∧ selectsDevice w d)
      (fun ret w =>
        let updated := { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
        ret = 0 ∧ w.dev = some (rootReplacementDevice v4 updated pid p id n) ∧
          RootReplacementEffects v4 updated id (rootReplacementDevice v4 updated pid p id n)) := by
  intro w ambient pre
  obtain ⟨ret, final, after, run, result, device⟩ :=
    setDevice_replace_root v4 key pid d p id n found peer listed resident leaf parent live bounded down w ambient pre
  exact ⟨ret, final, after, run, result, device, rootReplacement_effects v4 _ pid p id n peer⟩


/-- The original quiet-removal domain now has exact refusal or normal effects; totality was refuted. -/
theorem original_peer_remove_quiet (pid : PeerId) (d removed : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (empty : p.keypairNext = none ∧ p.keypairPrevious = none ∧ p.keypairCurrent = none)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = [])
    (steps : RemovalEffect (unlistPeer d pid) p.allowedipsList removed) :
    Campaign2.Observes (peerRemove (some pid)) (fun s => s.wg.device = some d)
      (fun _ out => quietRemovalOutcome (deadPeerDevice removed pid p) pid
        {erasePeerList p.allowedipsList p with isDead := true} out) :=
  peerRemove_quiet_returns pid d removed p resident live count empty send clear steps

end Leanux.Proofs.WG.Config.SourceClaims
