import Leanux.Proofs.WG.Config.KeyInstall
import Leanux.Proofs.WG.Config.DumpCancellation
import Leanux.Proofs.WG.Config.ClaimView
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Identity and quiet-installation claims over the WireGuard projection,
plus the unchanged empty-dump findings. -/
namespace Leanux.Proofs.WG.Config.SourceClaims
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Cookie-key precomputation returns normally. It changes only the device
cookie-encryption and MAC1 keys, to the specified public-key hashes when identity
exists and to zero otherwise. -/
theorem original_cookie_precomputation_return (d : Device) :
    Campaign2.Returns cookiePrecomputeDeviceKeys (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some (cookieKeysAfter d)) :=
  cookiePrecompute_returns d


/-- Identity installation returns normally, clamps the private bytes and
sets the public identity as specified, preserving all other device fields. -/
theorem original_identity_install_return (key : Key) (d : Device) :
    Campaign2.Returns (setStaticIdentityPrivateKey key) (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some { d with staticIdentity := identityAfter key d.staticIdentity }) :=
  setStaticIdentity_returns key d


/-- A private-key-only request equal byte-for-byte to the stored private key
returns normally and changes only the device generation. Equality is against
the raw request, not a normalized equivalence class of keys. -/
theorem original_unchanged_private_key_return (d : Device) (key : Key)
    (same : d.staticIdentity.staticPrivate = key) :
    Campaign2.Returns (wgSetDevice (privateKeyAttrs d key))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.wg.device = some { d with deviceUpdateGen := d.deviceUpdateGen + 1 }) :=
  setDevice_private_unchanged d key same


/-- Static-static precomputation for a resident peer returns normally with
the exact ordered peer-store updates, including the intermediate DH write
before zeroing a null result. All surrounding device fields are preserved. -/
theorem original_static_precomputation_return (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Returns (precomputeStaticStatic pid) (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some (precomputeDevice d pid p)) :=
  precomputeStaticStatic_returns pid d p resident


/-- Normal completion of expiry removes the peer's handshake entries, zeros
handshake fields, preserves its slots, and invalidates next/current sending keys.
The exact store transformation preserves all other fields except last-sent time.
Its existential clock parameter does not constrain that time or prove clock-read
provenance. Missing keypair targets can stop; no return guarantee is claimed. -/
theorem original_expiry_store_effects (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (expireCurrentPeerKeypairs pid) (fun w => w.wg.device = some d)
      (fun _ w => ∃ now, w.wg.device = some (expiredDevice d pid p now)) :=
  expireCurrent_exact pid d p resident


/-- Exact source equality exposing identity installation and the peer-list
loop after optional self-peer removal, before later peer attributes. This is
unconditional; the effects below separately require normal completion. -/
theorem original_private_key_factor (a : DeviceAttrs) :
    deviceKeyFactoredSource a = deviceKeySource a :=
  deviceKey_loop_factor a


/-- With staged sending disabled, a completed peer update precomputes its
static-static value and performs the exact expiry store transformation. The
clock here is existential; the stronger per-expiry read relation is separate. -/
theorem original_quiet_key_peer (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (keyPeerSource pid false) (fun w => w.wg.device = some d)
      (fun _ w => ∃ now, w.wg.device = some (peerUpdatedDevice d pid p now)) :=
  keyPeer_quiet_exact pid d p resident


/-- A completed quiet peer-list loop has the ordered relational effects of
each resident peer update. Repeated peers and aliased keypair slots are allowed;
missing peers or hidden inputs may stop, so this is not a return guarantee. -/
theorem original_quiet_key_peer_loop (pids : List PeerId) (d : Device) :
    Campaign2.Ensures (keyPeerLoopSource pids false) (fun w => w.wg.device = some d)
      (fun _ w => ∃ final, w.wg.device = some final ∧ KeyPeerUpdates d pids final) :=
  keyPeerLoop_quiet pids d


/-- The quiet installation block sets identity and cookie keys, then applies
ordered precomputation/expiry to its snapshotted peer list. The initial device
is after optional collision removal; later peer attributes are outside this
block. Normal completion is assumed, and clock values remain existential. -/
theorem original_quiet_key_install (d : Device) (key : Key)
    (quiet : requestsStagedSend d key = false) :
    Campaign2.Ensures (keyInstallSource key) (fun w => w.wg.device = some d)
      (fun _ w => ∃ final, w.wg.device = some final ∧
        KeyPeerUpdates (installedDevice d key) d.peerList final) :=
  keyInstall_quiet d key quiet


/-- A single empty-device getter is accepted from the runner's ordinary
fixture with an empty hidden record list. This establishes reachability of the
cancelled-nest accounting case, not a changed external observation. -/
theorem empty_dump_trace_accepted : DumpCancellation.accepted = true :=
  DumpCancellation.emptyTrace_accepted


/-- The original empty-device dump callback completes with one message,
a cleared cursor and 3720 bytes of tailroom. This retains the cancelled nest's
four bytes; the source correspondence discrepancy is recorded in request 3. -/
theorem original_empty_dump_room : DumpCancellation.callbackResult = some (0, 3720, true, 1) :=
  DumpCancellation.emptyDump_room


/-- The C-derived accounting of the retained header and attributes leaves
3724 bytes, exactly one cancelled nest header more than the mirror witness.
This is arithmetic supporting the source review, not a formal C simulation. -/
theorem empty_dump_cancellation_accounting :
    DumpCancellation.cancelledNestRoom = 3724 ∧ 3720 + nlaTotal 0 = DumpCancellation.cancelledNestRoom :=
  DumpCancellation.cancellation_accounting


end Leanux.Proofs.WG.Config.SourceClaims
