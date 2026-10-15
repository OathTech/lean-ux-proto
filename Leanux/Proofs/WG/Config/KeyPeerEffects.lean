import Leanux.Proofs.WG.Config.StagedInvalid

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem invalidateDevice_peers (d : Device) (kp : Option KeypairId) :
    (invalidateDevice d kp).peers = d.peers := by
  cases kp with
  | none => rfl
  | some id => cases found : d.keypairs[id]? <;> simp [invalidateDevice, found]

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

theorem keyPeer_complete (pid : PeerId) (d : Device) (p : Peer) (sendStaged : Bool)
    (resident : d.peers[pid]? = some p) :
    Ensures (keyPeerSource pid sendStaged) (fun w => w.k.wg = some d)
      (fun _ w => ∃ expiryNow queueNow,
        w.k.wg = some (keyPeerDevice d pid p expiryNow sendStaged queueNow)) := by
  have hp := (returns_iff _ _ _).mp (precomputeStaticStatic_returns pid d p resident)
  have he := (ensures_iff _ _ _).mp (expireCurrent_exact pid (precomputeDevice d pid p)
    { p with precomputedStaticStatic := precomputedAfter d.staticIdentity p } (precomputeDevice_peer pid d p))
  have head : Ensures (do precomputeStaticStatic pid; expireCurrentPeerKeypairs pid)
      (fun w => w.k.wg = some d)
      (fun _ w => ∃ now, w.k.wg = some (peerUpdatedDevice d pid p now)) := by
    rw [ensures_iff]
    mvcgen [hp, he]
  have factor : keyPeerSource pid sendStaged = ((do
      precomputeStaticStatic pid
      expireCurrentPeerKeypairs pid) >>= fun _ => do
        if ← branch .setDevSendStagedPeer sendStaged then sendStagedPackets pid) := by
    simp [keyPeerSource, bind_assoc]
  rw [factor]
  refine ensures_bind (R := fun (_ : Unit) w => ∃ expiryNow queueNow,
    w.k.wg = some (keyPeerDevice d pid p expiryNow sendStaged queueNow)) _ _ head ?_
  intro _ w ret v pre run
  obtain ⟨now, hd⟩ := pre
  have hs := (ensures_iff _ _ _).mp
    (staged_invalid pid (peerUpdatedDevice d pid p now) (updatedPeer d p now)
      (peerUpdatedDevice_peer d pid p now) (peerUpdatedDevice_invalid d pid p now))
  have tail : Ensures (do if ← branch .setDevSendStagedPeer sendStaged then sendStagedPackets pid)
      (fun w => w.k.wg = some (peerUpdatedDevice d pid p now))
      (fun _ w => ∃ queueNow, w.k.wg = some (keyPeerDevice d pid p now sendStaged queueNow)) := by
    rw [ensures_iff]
    cases sendStaged <;> mvcgen [branch, hs]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [keyPeerDevice, updatedPeer, zeroedHandshake]
    all_goals by_cases empty : p.staged = [] <;> simp_all
  obtain ⟨queueNow, hv⟩ := tail w ret v hd run
  exact ⟨now, queueNow, hv⟩

end Leanux.Proofs.WG.Config
