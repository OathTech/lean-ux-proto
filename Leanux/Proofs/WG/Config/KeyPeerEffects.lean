import Leanux.Proofs.WG.Config.KeyFieldFrames
import Leanux.Proofs.WG.Config.StagedInvalid
import Leanux.Proofs.WG.Config.KeyPeerLoop

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def updatedPeer (d : Device) (p : Peer) (now : Int64) : Peer :=
  { zeroedHandshake { p with precomputedStaticStatic := precomputedAfter d.staticIdentity p } with
    lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64 }

theorem peerUpdatedDevice_peer (d : Device) (pid : PeerId) (p : Peer) (now : Int64) :
    (peerUpdatedDevice d pid p now).peers[pid]? = some (updatedPeer d p now) := by
  simp [peerUpdatedDevice, expiredDevice, invalidateDevice_peers, expiryHeadDevice, withPeer, updatedPeer]

theorem peerUpdatedDevice_invalid (d : Device) (pid : PeerId) (p : Peer) (now : Int64)
    (id : KeypairId) (k : Keypair)
    (current : (updatedPeer d p now).keypairCurrent = some id)
    (found : (peerUpdatedDevice d pid p now).keypairs[id]? = some k) :
    k.sending.isValid = false := by
  have hk := expiredDevice_keypair (precomputeDevice d pid p) pid
    { p with precomputedStaticStatic := precomputedAfter d.staticIdentity p } now id
  have hc : p.keypairCurrent = some id := current
  change (expiredDevice _ _ _ _).keypairs[id]? = some k at found
  rw [hk] at found
  simp only [hc, or_true, ite_true] at found
  obtain ⟨old, _, rfl⟩ := Option.map_eq_some_iff.mp found
  rfl

def keyPeerDevice (d : Device) (pid : PeerId) (p : Peer)
    (expiryNow : Int64) (sendStaged : Bool) (queueNow : Int64) : Device :=
  let updated := peerUpdatedDevice d pid p expiryNow
  if sendStaged && !p.staged.isEmpty then
    invalidStagedDevice updated pid (updatedPeer d p expiryNow) queueNow
  else updated

private theorem keyPeerHead_complete (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (do precomputeStaticStatic pid; expireCurrentPeerKeypairs pid)
      (fun g => g.dev = some d)
      (fun _ g => ∃ now, g.dev = some (peerUpdatedDevice d pid p now)) := by
  have precompute : Ensures (precomputeStaticStatic pid) (fun g => g.dev = some d)
      (fun _ g => g.dev = some (precomputeDevice d pid p)) := by
    intro g ambient result final after device run
    obtain ⟨value, done, ending, execution, post⟩ := precomputeStaticStatic_returns pid d p resident g ambient device
    rw [run] at execution
    cases execution
    exact post
  exact ensures_bind _ _ precompute (fun _ => expireCurrent_exact pid (precomputeDevice d pid p)
    {p with precomputedStaticStatic := precomputedAfter d.staticIdentity p} (precomputeDevice_peer pid d p))

/-- Only the optional staged suffix is decorated; expiry and precomputation are
executed in their original order. -/
def observedKeyPeerSource (pid : PeerId) (sendStaged : Bool) : WG.M (Option (Int64 × Option Bool)) := do
  precomputeStaticStatic pid
  expireCurrentPeerKeypairs pid
  if ← branch .setDevSendStagedPeer sendStaged then observedInvalidStaged pid else pure none

/-- The actual ordered key effects, followed by the actual optional fallback
observation. The expiry clock remains an existential effect parameter. -/
def keyPeerObservation (d : Device) (pid : PeerId) (p : Peer) (sendStaged : Bool)
    (observation : Option (Int64 × Option Bool)) (s : Campaign2.Snapshot) : Prop :=
  ∃ expiryNow,
    if sendStaged then
      invalidStagedObservation (peerUpdatedDevice d pid p expiryNow) pid
        (updatedPeer d p expiryNow) observation s
    else observation = none ∧ s.wg.device = some (peerUpdatedDevice d pid p expiryNow)

/-- Erasure retains every actual prefix and suffix error; invalidity needed by
the specialized observer follows from the actual expiry prefix. -/
theorem observedKeyPeerSource_erase (pid : PeerId) (d : Device) (p : Peer) (sendStaged : Bool)
    (resident : d.peers[pid]? = some p) (g : WGWorld) (ambient : Ambient)
    (device : g.dev = some d) :
    (((do let _ ← observedKeyPeerSource pid sendStaged; pure ()) : WG.M Unit).run g).run ambient =
      ((keyPeerSource pid sendStaged).run g).run ambient := by
  have left : (do let _ ← observedKeyPeerSource pid sendStaged; pure ()) = ((do
      precomputeStaticStatic pid
      expireCurrentPeerKeypairs pid) >>= fun _ => do
        if ← branch .setDevSendStagedPeer sendStaged then
          let _ ← observedInvalidStaged pid
          pure ()
        else pure ()) := by
    cases sendStaged <;> simp [observedKeyPeerSource, branch, AmbientM.branch, bind_assoc]
  have right : keyPeerSource pid sendStaged = ((do
      precomputeStaticStatic pid
      expireCurrentPeerKeypairs pid) >>= fun _ => do
        if ← branch .setDevSendStagedPeer sendStaged then sendStagedPackets pid) := by
    simp [keyPeerSource, bind_assoc]
  rw [left, right]
  change (((((do precomputeStaticStatic pid; expireCurrentPeerKeypairs pid) : WG.M Unit).run g).run ambient) >>= _) =
    (((((do precomputeStaticStatic pid; expireCurrentPeerKeypairs pid) : WG.M Unit).run g).run ambient) >>= _)
  cases headRun : (((do precomputeStaticStatic pid; expireCurrentPeerKeypairs pid) : WG.M Unit).run g).run ambient with
  | error err => rfl
  | ok pair =>
    obtain ⟨⟨value, current⟩, inputs⟩ := pair
    obtain ⟨now, state⟩ := keyPeerHead_complete pid d p resident g ambient value current inputs device headRun
    cases sendStaged with
    | false => rfl
    | true =>
      simp only [branch, AmbientM.branch]
      exact observedInvalidStaged_erase pid (peerUpdatedDevice d pid p now) (updatedPeer d p now)
        (peerUpdatedDevice_peer d pid p now) (peerUpdatedDevice_invalid d pid p now)
        current _ state

/-- Semantic correction: optional staged sending follows its recorded queue
inspection, not the historical pending-flag prediction. -/
theorem keyPeer_complete (pid : PeerId) (d : Device) (p : Peer) (sendStaged : Bool)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (observedKeyPeerSource pid sendStaged) (fun s => s.wg.device = some d)
      (keyPeerObservation d pid p sendStaged) := by
  intro g ambient observation final after device run
  change g.dev = some d at device
  have factor : observedKeyPeerSource pid sendStaged = ((do
      precomputeStaticStatic pid
      expireCurrentPeerKeypairs pid) >>= fun _ => do
        if ← branch .setDevSendStagedPeer sendStaged then observedInvalidStaged pid else pure none) := by
    simp [observedKeyPeerSource, bind_assoc]
  rw [factor] at run
  change (((((do precomputeStaticStatic pid; expireCurrentPeerKeypairs pid) : WG.M Unit).run g).run ambient) >>= _) = _ at run
  cases headRun : (((do precomputeStaticStatic pid; expireCurrentPeerKeypairs pid) : WG.M Unit).run g).run ambient with
  | error err => rw [headRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨value, current⟩, inputs⟩ := pair
    obtain ⟨now, state⟩ := keyPeerHead_complete pid d p resident g ambient value current inputs device headRun
    rw [headRun] at run
    refine ⟨now, ?_⟩
    cases sendStaged with
    | false =>
      simp [branch, AmbientM.branch] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨rfl, state⟩
    | true =>
      simp [branch, AmbientM.branch] at run
      exact staged_invalid pid (peerUpdatedDevice d pid p now) (updatedPeer d p now)
        (peerUpdatedDevice_peer d pid p now) (peerUpdatedDevice_invalid d pid p now)
        current _ observation final after state run

end Leanux.Proofs.WG.Config
