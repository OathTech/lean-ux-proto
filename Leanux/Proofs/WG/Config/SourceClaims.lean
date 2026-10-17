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

/-- Every normally completed original expiry run has an actual prefix and
reset-clock read whose returned value determines the final store, including
last-sent time minus six seconds in wrapping Int64 arithmetic. The read is tied
to that run; this is not merely an unconstrained existential timestamp. -/
theorem original_expiry_clock_relation (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (w v : World) (device : w.k.wg = some d)
    (run : (expireCurrentPeerKeypairs pid).run w = .ok ((), v)) :
    ∃ now before after,
      (expiryReadPrefix pid).run w = .ok ((), before) ∧
      (hiddenClock64 .resetLastSent).run before = .ok (now, after) ∧
      v.k.wg = some (expiredDevice d pid p now) :=
  expireCurrent_clock pid d p resident w v device run


/-- The original non-retry handshake queue call resets attempts, reads the
age-test clock, and has the exact Device effect selected by that actual read:
no queue change, a balanced pending reference pair, or a fresh queued reference.
World bookkeeping and record availability are outside this normal-run claim. -/
theorem original_queued_handshake_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (w v : World) (device : w.k.wg = some d)
    (run : (sendQueuedHandshakeInitiation pid false).run w = .ok ((), v)) :
    ∃ now before after,
      (queuedReadPrefix pid).run w = .ok ({ p with timerHandshakeAttempts := 0 }, before) ∧
      (hiddenClock64 .birthdateExpired).run before = .ok (now, after) ∧
      v.k.wg = some (queuedDevice (withPeer d pid { p with timerHandshakeAttempts := 0 })
        pid { p with timerHandshakeAttempts := 0 } now) :=
  sendQueued_clock pid d p resident w v device run


/-- Original staging with absent or invalid current sending material either
returns unchanged for an empty staged list, or restores packets and has the
specified handshake-queue Device effects. Temporary key references preserve
lookups. Dangling current slots cannot complete with nonempty staging. Clock
values here are existential; World bookkeeping and record consumption are not
characterized, and no return guarantee is claimed. -/
theorem original_staged_invalid_key (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (invalid : ∀ id k, p.keypairCurrent = some id → d.keypairs[id]? = some k → k.sending.isValid = false) :
    Ensures (sendStagedPackets pid) (fun w => w.k.wg = some d)
      (fun _ w => if p.staged = [] then w.k.wg = some d
        else ∃ now, w.k.wg = some (invalidStagedDevice d pid p now)) :=
  staged_invalid pid d p resident invalid


/-- Both branches of the original key-update peer body have the specified
Device effects: precomputation, expiry, and optional staged-packet restoration
and handshake queueing. The clocks are existential and completion is assumed. -/
theorem original_key_peer_effects (pid : PeerId) (d : Device) (p : Peer) (sendStaged : Bool)
    (resident : d.peers[pid]? = some p) :
    Ensures (keyPeerSource pid sendStaged) (fun w => w.k.wg = some d)
      (fun _ w => ∃ expiryNow queueNow,
        w.k.wg = some (keyPeerDevice d pid p expiryNow sendStaged queueNow)) :=
  keyPeer_complete pid d p sendStaged resident


/-- The original peer-list loop realizes the ordered Device relation for
both staged-send settings. Repeated peers and keypair aliases are permitted.
This normal-completion result does not assert aggregate clock provenance. -/
theorem original_key_peer_loop_effects (pids : List PeerId) (d : Device) (sendStaged : Bool) :
    Ensures (keyPeerLoopSource pids sendStaged) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ KeyPeerRun sendStaged d pids final) :=
  keyPeerLoop_complete pids d sendStaged


/-- The installation block composes identity and cookie keys with the full
snapshotted peer-list relation, using the code's staged-send condition. The
baseline is after optional self-peer removal and before later peer attributes;
this is a Device-state normal-completion contract for that block. -/
theorem original_key_install_effects (d : Device) (key : Key) :
    Ensures (keyInstallSource key) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        KeyPeerRun (requestsStagedSend d key) (installedDevice d key) d.peerList final) :=
  keyInstall_complete d key


/-- A changed private-key-only outer request with no generated-public-key
peer-table match returns zero on normal completion, increments generation, and
performs the full installation relation including optional staged sending.
The raw request differs from the stored key; no peer-removal arm is taken.
This does not guarantee input records or establish aggregate clock provenance. -/
theorem original_private_key_request_no_collision (d : Device) (key : Key)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key) :
    Ensures (wgSetDevice (privateKeyAttrs d key))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ ∃ final, w.k.wg = some final ∧
        KeyPeerRun (requestsStagedSend d key) (installedDevice (requestGeneration d) key) d.peerList final) :=
  setDevice_private_changed_no_collision d key changed absent


/-- A fresh original callback for one resident peer without allowed IPs
returns all fixed device and peer attributes, completes its cursor and preserves
the device. The bound reserves room for the transport's final DONE message. -/
theorem original_single_peer_dump_callback (pid : PeerId) (d : Device) (p : Peer)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (empty : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE) :
    Returns (wgGetDeviceDump { hasWg := true } 0 {}) (fun w => w.k.wg = some d)
      (fun result w => result = singlePeerDump d p ∧ w.k.wg = some d) :=
  wgGetDeviceDump_single pid d p peers resident empty room


/-- The original public getter for one resident peer without allowed IPs
returns exact canonical JSON, including the empty allowed-IP array, preserves
the device and leaves socket 7 drained and finished. The socket starts idle
with an empty queue; its bound flag is unrestricted. This is a total-return
contract for one complete chunk, not a multipart snapshot theorem. -/
theorem original_single_peer_getter (pid : PeerId) (d : Device) (p : Peer) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (noIps : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Returns (wgGetDevice (byIndex d))
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = sock ∧ selectsDevice w d)
      (fun result w => result = .ok (singlePeerJson d p) ∧ w.k.wg = some d ∧
        w.k.nlSock7 = { completedSock sock d p with queue := [] }) :=
  wgGetDevice_single pid d p sock peers resident noIps room idle empty


/-- Setting an existing stopped peer's preshared key and keepalive interval,
then calling the original public getter after either setter return, returns the
exact applied configuration
and a drained socket. A malformed second peer entry makes the setter return
EINVAL but does not roll back the first update; the same readback holds.
The bound on the live reference count guarantees the temporary lookup reference
can be acquired. The single peer has no allowed IPs and fits one dump chunk. -/
theorem original_scalar_get_after_set (d : Device) (key psk : Key) (interval : Nat) (bad : Bool)
    (pid : PeerId) (p : Peer) (sock : NlSock)
    (peers : d.peerList = [pid])
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (noIps : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Returns (do
      let ret ← wgSetDevice (scalarDeviceAttrs d key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = sock ∧ selectsDevice w d)
      (fun result w =>
        let updated := scalarRequestDevice d pid p psk interval
        let configured := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        result = ((if bad then -EINVAL else 0), .ok (singlePeerJson updated configured)) ∧
          w.k.wg = some updated ∧
          w.k.nlSock7 = { completedSock sock updated configured with queue := [] }) :=
  scalar_outer_get_after_set d key psk interval bad pid p sock peers found resident live bounded
    down noIps room idle empty


/-- Replacing a stopped peer's singleton root-leaf allowed-IP list with an
empty list removes the node, clears its family root, increments the trie
sequence, and removes that node from every peer list. The public device
setter increments its generation and balances the lookup reference. -/
theorem original_allowedips_replace_single_root (v4 : Bool) (key : Key) (pid : PeerId)
    (d : Device) (p : Peer) (id : NodeId) (n : AipNode)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (peer : d.peers[pid]? = some p) (listed : p.allowedipsList = [id])
    (resident : d.nodes[id]? = some n) (leaf : n.bit = #[none, none])
    (parent : n.parent = rootSlot v4) (owned : n.peer = some pid)
    (root : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = some id)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Returns (wgSetDevice (replaceAllowedipsDeviceAttrs d key))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w =>
        let updated := { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
        ret = 0 ∧ w.k.wg = some (rootReplacementDevice v4 updated pid p id n) ∧
          RootReplacementEffects v4 updated id (rootReplacementDevice v4 updated pid p id n)) := by
  intro w pre
  obtain ⟨ret, final, run, result, device⟩ :=
    setDevice_replace_root v4 key pid d p id n found peer listed resident leaf parent live bounded down w pre
  exact ⟨ret, final, run, result, device, rootReplacement_effects v4 _ pid p id n peer⟩


/-- Original peer removal returns for an empty-slot peer with empty send/clear
queues and a supplied allowed-IP removal witness. The exact Device performs
membership/death updates, three slot writes, five timer deletions, the empty
drain, peer-count decrement and final release in source order. Final release
erases the peer only on its last reference; otherwise the dead peer remains.
This is a Device contract, not a whole-World frame, a claim about every pending
flag or a theorem for queued work and live keypair slots. -/
theorem original_peer_remove_quiet (pid : PeerId) (d removed : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (empty : p.keypairNext = none ∧ p.keypairPrevious = none ∧ p.keypairCurrent = none)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = [])
    (steps : RemovalEffect (unlistPeer d pid) p.allowedipsList removed) :
    Returns (peerRemove (some pid)) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (quietRemovedDevice (deadPeerDevice removed pid p) pid
        { erasePeerList p.allowedipsList p with isDead := true })) :=
  peerRemove_quiet_returns pid d removed p resident live count empty send clear steps

end Leanux.Proofs.WG.Config.SourceClaims
