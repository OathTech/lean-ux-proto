import Leanux.Proofs.WG.Config.ExpiryEffects
import Leanux.Proofs.WG.Config.AllowedGeneralReplacement
import Leanux.Proofs.WG.Config.PeerDead
import Leanux.Proofs.WG.Config.ClaimView
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.SourceClaims
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- On normal completion, expiry changes only sending validity in current
and next keypair entries. Every other keypair field and lookup is preserved.
Aliased slots are covered by the union of the two target identities. -/
theorem original_expiry_keypair_fields (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (q : KeypairId) :
    Campaign2.Ensures (expireCurrentPeerKeypairs pid) (fun w => w.wg.device = some d)
      (fun _ w => (w.wg.device.bind fun dev => dev.keypairs[q]?) = (d.keypairs[q]?).map fun k =>
        if p.keypairNext = some q ∨ p.keypairCurrent = some q then
          { k with sending := { k.sending with isValid := false } } else k) := by
  intro w ambient ret v after hp hr
  obtain ⟨now, hv⟩ := expireCurrent_exact pid d p resident w ambient ret v after hp hr
  simpa [Campaign2.snapshot, Campaign2.core, hv] using expiredDevice_keypair d pid p now q

/-- A supplied pure removal witness covers every structural branch and the evolving
snapshot loop. The original operation returns, filters the removed identities from
every peer list, clears every processed node owner, empties the target list and
increments the sequence once exactly
when the snapshot was nonempty. This does not establish witness existence for all
valid tries, trie validity, lookup preservation or ownership/list coherence. -/
theorem original_allowedips_remove_general (pid : PeerId) (p : Peer) (d final : Device)
    (resident : d.peers[pid]? = some p) (steps : RemovalEffect d p.allowedipsList final) :
    Campaign2.Returns (removeByPeer pid) (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some final ∧
        (∀ other : PeerId, final.peers[other]? = d.peers[other]?.map (erasePeerList p.allowedipsList)) ∧
        final.peers[pid]? = some (erasePeerList p.allowedipsList p) ∧
        (erasePeerList p.allowedipsList p).allowedipsList = [] ∧
        final.peerAllowedips.seq = d.peerAllowedips.seq + (if p.allowedipsList.isEmpty then 0 else 1) ∧
        ∀ id ∈ p.allowedipsList, nodeOwner final id = none) := by
  intro w ambient pre
  obtain ⟨ret, result, after, run, device⟩ := removeByPeer_general pid p d final resident steps w ambient pre
  refine ⟨ret, result, after, run, device, removalEffect_peers steps, ?_,
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
    Campaign2.Returns (wgSetDevice (replaceAllowedipsDeviceAttrs d key))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.wg.device = some (generalReplacementDevice removed pid p) ∧
        ∃ q, (generalReplacementDevice removed pid p).peers[pid]? = some q ∧
          q.allowedipsList = [] ∧ q.refcount = p.refcount ∧ q.internalId = p.internalId ∧
          ∀ id ∈ p.allowedipsList, nodeOwner (generalReplacementDevice removed pid p) id = none) := by
  intro w ambient pre
  obtain ⟨ret, result, after, run, value, device⟩ :=
    setDevice_replace_general key pid d removed p found resident live bounded down steps w ambient pre
  obtain ⟨q, peer, empty, refs, identity⟩ := generalReplacement_peer removed pid p
  refine ⟨ret, result, after, run, value, device, q, peer, empty, refs, identity, ?_⟩
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
    Campaign2.Returns (peerMakeDead pid) (fun w => w.wg.device = some d)
      (fun _ w =>
        let final := deadPeerDevice removed pid p
        w.wg.device = some final ∧
        final.peerList = d.peerList.filter (· != pid) ∧
        final.peerHashtable = d.peerHashtable.filter (·.2 != pid) ∧
        final.indexTable = d.indexTable ∧ final.numPeers = d.numPeers ∧
        final.peers[pid]? = some { erasePeerList p.allowedipsList p with isDead := true } ∧
        (erasePeerList p.allowedipsList p).allowedipsList = [] ∧
        (erasePeerList p.allowedipsList p).refcount = p.refcount ∧
        (∀ id ∈ p.allowedipsList, nodeOwner final id = none)) := by
  intro w ambient pre
  obtain ⟨ret, final, after, run, device⟩ := peerMakeDead_returns pid p d removed resident steps w ambient pre
  exact ⟨ret, final, after, run, device, deadPeerDevice_effects pid p d removed steps⟩

end Leanux.Proofs.WG.Config.SourceClaims
