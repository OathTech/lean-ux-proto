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

/-- On normal completion, expiry changes only sending validity in current
and next keypair entries. Every other keypair field and lookup is preserved.
Aliased slots are covered by the union of the two target identities. -/
theorem original_expiry_keypair_fields (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (q : KeypairId) :
    Ensures (expireCurrentPeerKeypairs pid) (fun w => w.k.wg = some d)
      (fun _ w => (w.k.wg.bind fun dev => dev.keypairs[q]?) = (d.keypairs[q]?).map fun k =>
        if p.keypairNext = some q ∨ p.keypairCurrent = some q then
          { k with sending := { k.sending with isValid := false } } else k) := by
  intro w ret v hp hr
  obtain ⟨now, hv⟩ := expireCurrent_exact pid d p resident w ret v hp hr
  simpa [hv] using expiredDevice_keypair d pid p now q


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


/-- A supplied pure removal witness covers every structural branch and the evolving
snapshot loop. The original operation returns, filters the removed identities from
every peer list, clears every processed node owner, empties the target list and
increments the sequence once exactly
when the snapshot was nonempty. This does not establish witness existence for all
valid tries, trie validity, lookup preservation or ownership/list coherence. -/
theorem original_allowedips_remove_general (pid : PeerId) (p : Peer) (d final : Device)
    (resident : d.peers[pid]? = some p) (steps : RemovalEffect d p.allowedipsList final) :
    Returns (removeByPeer pid) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some final ∧
        (∀ other : PeerId, final.peers[other]? = d.peers[other]?.map (erasePeerList p.allowedipsList)) ∧
        final.peers[pid]? = some (erasePeerList p.allowedipsList p) ∧
        (erasePeerList p.allowedipsList p).allowedipsList = [] ∧
        final.peerAllowedips.seq = d.peerAllowedips.seq + (if p.allowedipsList.isEmpty then 0 else 1) ∧
        ∀ id ∈ p.allowedipsList, nodeOwner final id = none) := by
  intro w pre
  obtain ⟨ret, result, run, device⟩ := removeByPeer_general pid p d final resident steps w pre
  refine ⟨ret, result, run, device, removalEffect_peers steps, ?_,
    erasePeerList_own_empty p, removalEffect_seq steps,
    fun id member => removalEffect_owner_none steps id (Or.inl member)⟩
  simpa [resident] using removalEffect_peers steps pid


/-- The public setter replaces an existing stopped peer's allowed-IP list by the
empty list for any supplied pure removal witness. The lookup reference is balanced
and peer identity is preserved; every processed node is absent or unowned.
Readiness is checked on successive maps, including
the acquired reference and updated generation; no global trie invariant or general
existence of a removal witness is claimed. -/
theorem original_allowedips_replace_general (key : Key) (pid : PeerId) (d removed : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (steps : RemovalEffect
      (withPeer { d with deviceUpdateGen := d.deviceUpdateGen + 1 } pid { p with refcount := p.refcount + 1 })
      p.allowedipsList removed) :
    Returns (wgSetDevice (replaceAllowedipsDeviceAttrs d key))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.k.wg = some (generalReplacementDevice removed pid p) ∧
        ∃ q, (generalReplacementDevice removed pid p).peers[pid]? = some q ∧
          q.allowedipsList = [] ∧ q.refcount = p.refcount ∧ q.internalId = p.internalId ∧
          ∀ id ∈ p.allowedipsList, nodeOwner (generalReplacementDevice removed pid p) id = none) := by
  intro w pre
  obtain ⟨ret, result, run, value, device⟩ :=
    setDevice_replace_general key pid d removed p found resident live bounded down steps w pre
  obtain ⟨q, peer, empty, refs, identity⟩ := generalReplacement_peer removed pid p
  refine ⟨ret, result, run, value, device, q, peer, empty, refs, identity, ?_⟩
  intro id member
  exact removalEffect_owner_none steps id (Or.inl member)


/-- Original peer death removes the identity from the device peer list and
public-key table, performs the witnessed allowed-IP removal and sets isDead.
The peer remains resident with its original reference count; the numeric index
table and device peer count are unchanged at this stage. Every processed node
is absent or unowned. This is peerMakeDead, before later keypair/timer/work
cleanup and final reference release; no complete peerRemove claim is made. -/
theorem original_peer_make_dead (pid : PeerId) (p : Peer) (d removed : Device)
    (resident : d.peers[pid]? = some p)
    (steps : RemovalEffect (unlistPeer d pid) p.allowedipsList removed) :
    Returns (peerMakeDead pid) (fun w => w.k.wg = some d)
      (fun _ w =>
        let final := deadPeerDevice removed pid p
        w.k.wg = some final ∧
        final.peerList = d.peerList.filter (· != pid) ∧
        final.peerHashtable = d.peerHashtable.filter (·.2 != pid) ∧
        final.indexTable = d.indexTable ∧ final.numPeers = d.numPeers ∧
        final.peers[pid]? = some { erasePeerList p.allowedipsList p with isDead := true } ∧
        (erasePeerList p.allowedipsList p).allowedipsList = [] ∧
        (erasePeerList p.allowedipsList p).refcount = p.refcount ∧
        (∀ id ∈ p.allowedipsList, nodeOwner final id = none)) := by
  intro w pre
  obtain ⟨ret, final, run, device⟩ := peerMakeDead_returns pid p d removed resident steps w pre
  exact ⟨ret, final, run, device, deadPeerDevice_effects pid p d removed steps⟩


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
