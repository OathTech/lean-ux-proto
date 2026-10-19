import Leanux.Proofs.WG.Origins.CurrentIdentity
import Leanux.Proofs.WG.Queues.AffiliationCompatibility
import Leanux.Proofs.WG.Packets.PublicationPeer

/-! A stronger local publication certificate uses one configured session
witness for material, owner and current allocation identity. Initialized
transport and the later routing/Stack join remain separate obligations. -/
namespace Leanux.Proofs.WG.PublicationIdentity
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Lifetimes

def CurrentCertificate (history : List SessionOrigin.Receipt) (id : SkbId)
    (r : WGRunWitness (RxPacket × Option RxPacket)) (out : RxPacket) (pid : PeerId)
    (v : WGWorld) : Prop :=
  ∃ d k p after,
    r.before.dev = some d ∧ d.rxSkbs[id]? = some r.value.1 ∧
    d.keypairs[r.value.1.keypair]? = some k ∧ k.receiving.isValid = true ∧
    pid = r.value.1.peer ∧
    CurrentIdentity.ByPeer history d.ifindex r.value.1.keypair k pid (fun q => d.peers[q]?) ∧
    out = {r.value.1 with nonce := u64le r.value.1.bytes 8, bytes := out.bytes} ∧
    aeadDecrypt k.receiving.key (counterNonce (u64le r.value.1.bytes 8))
      (r.value.1.bytes.drop 16) [] = some out.bytes ∧
    packetStamp v id = packetStamp r.before id ∧
    d.peers[pid]? = some p ∧ v.dev = some after ∧ after.ifindex = d.ifindex ∧
    after.rxSkbs[id]? = some {out with state := .crypted} ∧
    after.peers[pid]? = some {p with refcount := p.refcount + 1, napiScheduled := true}

theorem CurrentCertificate.historical {id : SkbId}
    (h : CurrentCertificate history id r out pid v) : Identity history id r out pid v := by
  obtain ⟨d, k, p, after, hd, hp, hk, valid, owner, supported, shape, aead,
    stamp, _, hv, epoch, packet, _⟩ := h
  exact ⟨d, k, hd, hp, hk, valid, owner, supported.configured,
    shape, aead, stamp, after, hv, epoch, packet⟩

/-- The published resident peer has the allocation stamp and static key of
the very Context supporting this certificate, even though its timer/reference
fields have changed since that session. -/
theorem CurrentCertificate.owner_identity {id : SkbId}
    (h : CurrentCertificate history id r out pid v) :
    ∃ (run : WGRunWitness (Option SessionOrigin.Context)) (ctx : SessionOrigin.Context)
      (after : Device) (peer : Peer),
      SessionOrigin.Receipt.material pid run ∈ history ∧
      run.Valid (SessionOrigin.front pid) ∧ run.value = some ctx ∧
      ConfiguredSession.Configured pid run.before ctx ∧
      v.dev = some after ∧ after.peers[pid]? = some peer ∧
      CurrentIdentity.identity peer = CurrentIdentity.identity ctx.peer := by
  obtain ⟨d, k, p, after, _, _, _, _, _, supported, _, _, _, hp, hv, _, _, finalPeer⟩ := h
  obtain ⟨run, ctx, originalDev, original, member, valid, value, _, configured,
    _, _, _, _, _, _, _, current⟩ := supported
  refine ⟨run, ctx, after, {p with refcount := p.refcount + 1, napiScheduled := true},
    member, valid, value, configured, hv, finalPeer, ?_⟩
  exact current p hp

/-- The material and current peer identity clauses share the same supporting
receipt. DEAD publication is excluded by the actual successful decrypt witness. -/
theorem published_current (history : List SessionOrigin.Receipt) (id : SkbId)
    (r : WGRunWitness (RxPacket × Option RxPacket)) (out : RxPacket) (pid : PeerId)
    (v : WGWorld) (ambient : Ambient)
    (support : CurrentIdentity.Inv history r.before) (compat : RxCredits.RxCompatible r.before)
    (published : Published id r out pid v ambient) :
    CurrentCertificate history id r out pid v := by
  obtain ⟨d, k, hd, hp, hk, valid, owner, _, shape, aead, stamp,
    packetAfter, hpacketAfter, packetEpoch, packet⟩ :=
    published_identity history id r out pid v ambient support.configured compat published
  obtain ⟨peerDev, peerKey, p, after, hpeerDev, _, hpeerKey, word, hpeer,
    hafter, epoch, finalPeer⟩ := published_peer id r out pid v ambient published
  have deviceEq : peerDev = d := Option.some.inj (hpeerDev.symm.trans hd)
  subst peerDev
  have keyEq : peerKey = k := Option.some.inj (hpeerKey.symm.trans hk)
  subst peerKey
  have afterEq : packetAfter = after := Option.some.inj (hpacketAfter.symm.trans hafter)
  subst packetAfter
  exact ⟨d, k, p, after, hd, hp, hk, valid, owner,
    (support d hd _ k hk valid).byPeer word, shape, aead, stamp,
    hpeer, hafter, epoch, packet, finalPeer⟩

theorem published_current_of_affiliation (history : List SessionOrigin.Receipt) (id : SkbId)
    (r : WGRunWitness (RxPacket × Option RxPacket)) (out : RxPacket) (pid : PeerId)
    (v : WGWorld) (ambient : Ambient)
    (support : CurrentIdentity.Inv history r.before) (affiliation : Affiliation.Inv r.before)
    (published : Published id r out pid v ambient) :
    CurrentCertificate history id r out pid v :=
  published_current history id r out pid v ambient support
    (RxCredits.rxCompatible_of_affiliation affiliation) published

end Leanux.Proofs.WG.PublicationIdentity
