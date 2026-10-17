import Leanux.Proofs.WG.Config.ExpiryReadSource

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def expiryHeadDevice (d : Device) (pid : PeerId) (p : Peer) (now : Int64) : Device :=
  let removed := { d with indexTable := d.indexTable.filter fun e => !(e.owner == .handshake pid) }
  let zeroed := withPeer removed pid (zeroedHandshake p)
  withPeer zeroed pid { zeroedHandshake p with
    lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64 }

def expiryHeadSource (pid : PeerId) : WG.M Unit := do
  requireNotPending pid "clearing the handshake"
  handshakeClear pid
  resetLastSentHandshake pid

theorem expiryHead_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (expiryHeadSource pid) (fun w => w.dev = some d)
      (fun _ w => ∃ now, w.dev = some (expiryHeadDevice d pid p now)) := by
  change Ensures (do expiryReadPrefix pid; resetLastSentHandshake pid) _ _
  refine ensures_bind _ _ (expiryReadPrefix_exact pid d p resident) ?_
  intro _
  unfold resetLastSentHandshake
  refine ensures_bind _ _
    ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hiddenClock64 .resetLastSent)
      (fun g : WGWorld => g.dev = some (expiryZeroDevice d pid p)))) ?_
  intro now g ambient result final after device run
  simp [getPeer, getDev, device, expiryZeroDevice, withPeer, setPeer, modifyDev] at run
  rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  exact ⟨now, rfl⟩

def invalidateDevice (d : Device) (kp : Option KeypairId) : Device :=
  match kp with
  | none => d
  | some id => match d.keypairs[id]? with
    | none => d
    | some k => { d with keypairs := d.keypairs.insert id { k with sending := { k.sending with isValid := false } } }

def invalidateSource (site : Decision) (kp : Option KeypairId) : WG.M Unit := do
  if ← branch site kp.isSome then
    let some id := kp | invariant "unreachable"
    let k ← getKeypair id
    setKeypair id { k with sending := { k.sending with isValid := false } }

theorem invalidate_exact (site : Decision) (kp : Option KeypairId) (d : Device) :
    Ensures (invalidateSource site kp) (fun w => w.dev = some d)
      (fun _ w => w.dev = some (invalidateDevice d kp)) := by
  intro g ambient result final after device run
  cases kp with
  | none =>
    simp [invalidateSource, branch, AmbientM.branch] at run
    rcases run with ⟨rfl, rfl⟩
    exact device
  | some id =>
    cases key : d.keypairs[id]? with
    | none =>
      simp [invalidateSource, getKeypair, getDev, device, key, branch, AmbientM.branch,
        invariant, AmbientM.invariant] at run
      cases run
    | some k =>
      simp [invalidateSource, getKeypair, getDev, device, key, branch, AmbientM.branch,
        setKeypair, modifyDev] at run
      rcases run with ⟨rfl, rfl⟩
      simp [invalidateDevice, key]

def expiryTailSource (pid : PeerId) : WG.M Unit := do
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
    simp only [invalidateSource, bind_assoc, Option.isSome_none, Option.isSome_some]
  all_goals congr 1
  all_goals funext value
  all_goals cases value <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc]

theorem expiryTail_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (expiryTailSource pid) (fun w => w.dev = some d)
      (fun _ w => w.dev = some (invalidateDevice (invalidateDevice d p.keypairNext) p.keypairCurrent)) := by
  unfold expiryTailSource
  refine ensures_bind (Q := fun q g => q = p ∧ g.dev = some d) _ _ ?_ ?_
  · intro g ambient q final after device run
    simp [getPeer, getDev, device, resident] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, device⟩
  · intro q g ambient result final after pre run
    obtain ⟨same, device⟩ := pre
    subst q
    exact ensures_bind _ _ (invalidate_exact .expireNextKeypair p.keypairNext d)
      (fun _ => invalidate_exact .expireCurrentKeypair p.keypairCurrent (invalidateDevice d p.keypairNext))
      g ambient result final after device run

def expiredDevice (d : Device) (pid : PeerId) (p : Peer) (now : Int64) : Device :=
  invalidateDevice (invalidateDevice (expiryHeadDevice d pid p now) p.keypairNext) p.keypairCurrent

theorem expireCurrent_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (expireCurrentPeerKeypairs pid) (fun w => w.dev = some d)
      (fun _ w => ∃ now, w.dev = some (expiredDevice d pid p now)) := by
  rw [expireCurrent_source]
  refine ensures_bind (R := fun (_ : Unit) g => ∃ now, g.dev = some (expiredDevice d pid p now))
    (expiryHeadSource pid) (fun _ => expiryTailSource pid) (expiryHead_exact pid d p resident) ?_
  intro _ g ambient ret final after pre run
  obtain ⟨now, device⟩ := pre
  let reset : Peer := { zeroedHandshake p with
    lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64 }
  have present : (expiryHeadDevice d pid p now).peers[pid]? = some reset := by
    simp [expiryHeadDevice, withPeer, reset]
  have post := expiryTail_exact pid (expiryHeadDevice d pid p now) reset present
    g ambient ret final after device run
  exact ⟨now, by simpa [expiredDevice, reset, zeroedHandshake] using post⟩

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
