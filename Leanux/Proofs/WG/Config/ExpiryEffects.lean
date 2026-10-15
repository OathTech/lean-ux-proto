import Leanux.Proofs.WG.Config.Precomputation

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def zeroedHandshake (p : Peer) : Peer :=
  { p with
    ephemeralPrivate := List.replicate 32 0
    remoteEphemeral := List.replicate 32 0
    hash := List.replicate 32 0
    chainingKey := List.replicate 32 0
    remoteIndex := 0
    handshakeState := 0 }

def expiryHeadDevice (d : Device) (pid : PeerId) (p : Peer) (now : Int64) : Device :=
  let removed := { d with indexTable := d.indexTable.filter fun e => !(e.owner == .handshake pid) }
  let zeroed := withPeer removed pid (zeroedHandshake p)
  withPeer zeroed pid { zeroedHandshake p with
    lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64 }

def expiryHeadSource (pid : PeerId) : M Unit := do
  requireNotPending pid "clearing the handshake"
  handshakeClear pid
  resetLastSentHandshake pid

theorem expiryHead_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (expiryHeadSource pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ now, w.k.wg = some (expiryHeadDevice d pid p now)) := by
  let zeroed := withPeer
    { d with indexTable := d.indexTable.filter fun e => !(e.owner == .handshake pid) }
    pid (zeroedHandshake p)
  have hh := hiddenClock64_kernel_spec (fun k => k.wg = some zeroed)
  rw [ensures_iff]
  noise_vcgen [expiryHeadSource, requireNotPending, handshakeClear, IndexOwner.peerDeref, IndexOwner.peerWord, unsupported, indexRemove,
    _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry, handshakeZero, resetLastSentHandshake,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, branch, invariant, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [expiryHeadDevice, zeroed, zeroedHandshake, withPeer]
  all_goals grind only

def invalidateDevice (d : Device) (kp : Option KeypairId) : Device :=
  match kp with
  | none => d
  | some id => match d.keypairs[id]? with
    | none => d
    | some k => { d with keypairs := d.keypairs.insert id { k with sending := { k.sending with isValid := false } } }

def invalidateSource (site : Decision) (kp : Option KeypairId) : M Unit := do
  if ← branch site kp.isSome then
    let some id := kp | invariant "unreachable"
    let k ← getKeypair id
    setKeypair id { k with sending := { k.sending with isValid := false } }

theorem invalidate_exact (site : Decision) (kp : Option KeypairId) (d : Device) :
    Ensures (invalidateSource site kp) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (invalidateDevice d kp)) := by
  rw [ensures_iff]
  cases kp <;> simp only [invalidateSource, Option.isSome_none, Option.isSome_some]
  all_goals mvcgen [getKeypair, getDev, getK, setKeypair, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [invalidateDevice]
  all_goals grind only

def expiryTailSource (pid : PeerId) : M Unit := do
  let p ← getPeer pid
  invalidateSource .expireNextKeypair p.keypairNext
  invalidateSource .expireCurrentKeypair p.keypairCurrent

theorem expireCurrent_source (pid : PeerId) :
    expireCurrentPeerKeypairs pid = (do expiryHeadSource pid; expiryTailSource pid) := by
  simp only [expireCurrentPeerKeypairs, expiryHeadSource, expiryTailSource, bind_assoc]
  congr 1
  funext _
  congr 1
  funext _
  congr 1
  funext _
  congr 1
  funext p
  cases hn : p.keypairNext <;> cases hc : p.keypairCurrent <;>
    simp [invalidateSource, branch, hn, hc, bind_assoc]

theorem expiryTail_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (expiryTailSource pid) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (invalidateDevice (invalidateDevice d p.keypairNext) p.keypairCurrent)) := by
  have hn := fun kp => (ensures_iff _ _ _).mp (invalidate_exact .expireNextKeypair kp d)
  have hc := fun kp => (ensures_iff _ _ _).mp
    (invalidate_exact .expireCurrentKeypair kp (invalidateDevice d p.keypairNext))
  rw [ensures_iff]
  mvcgen [expiryTailSource, getPeer, getDev, getK, invariant, hn, hc]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals grind only

def expiredDevice (d : Device) (pid : PeerId) (p : Peer) (now : Int64) : Device :=
  invalidateDevice (invalidateDevice (expiryHeadDevice d pid p now) p.keypairNext) p.keypairCurrent

theorem expireCurrent_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (expireCurrentPeerKeypairs pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ now, w.k.wg = some (expiredDevice d pid p now)) := by
  rw [expireCurrent_source]
  refine ensures_bind (R := fun (_ : Unit) w => ∃ now, w.k.wg = some (expiredDevice d pid p now))
    (expiryHeadSource pid) (fun _ => expiryTailSource pid) (expiryHead_exact pid d p resident) ?_
  intro _ w ret v hp hr
  obtain ⟨now, hw⟩ := hp
  let reset : Peer := { zeroedHandshake p with
    lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64 }
  have hresident : (expiryHeadDevice d pid p now).peers[pid]? = some reset := by
    simp [expiryHeadDevice, withPeer, reset]
  have hv := expiryTail_exact pid (expiryHeadDevice d pid p now) reset hresident w ret v hw hr
  exact ⟨now, by simpa [expiredDevice, reset, zeroedHandshake] using hv⟩

theorem invalidateDevice_lookup (d : Device) (kp : Option KeypairId) (q : KeypairId) :
    (invalidateDevice d kp).keypairs[q]? = (d.keypairs[q]?).map fun k =>
      if kp = some q then { k with sending := { k.sending with isValid := false } } else k := by
  cases kp with
  | none => simp [invalidateDevice]
  | some id =>
    cases h : d.keypairs[id]? <;> by_cases same : q = id <;>
      simp_all [invalidateDevice, Std.TreeMap.getElem?_insert, Ne.symm]

theorem expiredDevice_keypair (d : Device) (pid : PeerId) (p : Peer) (now : Int64) (q : KeypairId) :
    (expiredDevice d pid p now).keypairs[q]? = (d.keypairs[q]?).map fun k =>
      if p.keypairNext = some q ∨ p.keypairCurrent = some q then
        { k with sending := { k.sending with isValid := false } } else k := by
  simp only [expiredDevice, invalidateDevice_lookup]
  simp only [expiryHeadDevice, withPeer, Option.map_map, Function.comp_def]
  by_cases hn : p.keypairNext = some q <;> by_cases hc : p.keypairCurrent = some q <;> simp [hn, hc]

end Leanux.Proofs.WG.Config
