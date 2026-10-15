import Leanux.Proofs.WG.Config.ExpiryClock

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def keyPeerSource (pid : PeerId) (sendStaged : Bool) : M Unit := do
  precomputeStaticStatic pid
  expireCurrentPeerKeypairs pid
  if ← branch .setDevSendStagedPeer sendStaged then sendStagedPackets pid

def keyPeerLoopSource (pids : List PeerId) (sendStaged : Bool) : M Unit := do
  for pid in pids do
    _ ← branch .setDevKeyPeerIter true
    keyPeerSource pid sendStaged

def peerUpdatedDevice (d : Device) (pid : PeerId) (p : Peer) (now : Int64) : Device :=
  expiredDevice (precomputeDevice d pid p) pid
    { p with precomputedStaticStatic := precomputedAfter d.staticIdentity p } now

theorem keyPeer_quiet_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (keyPeerSource pid false) (fun w => w.k.wg = some d)
      (fun _ w => ∃ now, w.k.wg = some (peerUpdatedDevice d pid p now)) := by
  have hp := (returns_iff _ _ _).mp (precomputeStaticStatic_returns pid d p resident)
  have he := (ensures_iff _ _ _).mp (expireCurrent_exact pid (precomputeDevice d pid p)
    { p with precomputedStaticStatic := precomputedAfter d.staticIdentity p } (precomputeDevice_peer pid d p))
  rw [ensures_iff]
  simp [keyPeerSource, branch, bind_assoc]
  mvcgen [hp, he]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerUpdatedDevice]

theorem keyPeer_missing (pid : PeerId) :
    Ensures (keyPeerSource pid false) (fun w => peerAt w pid = none) (fun _ _ => False) := by
  have he := unconstrained_prefix (expireCurrentPeerKeypairs pid)
  rw [ensures_iff]
  simp [keyPeerSource, branch, bind_assoc]
  mvcgen [precomputeStaticStatic, requireNotPending, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, invariant, unsupported, he]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerAt]

theorem keyPeer_quiet_step (pid : PeerId) (d : Device) :
    Ensures (keyPeerSource pid false) (fun w => w.k.wg = some d)
      (fun _ w => ∃ p now, d.peers[pid]? = some p ∧ w.k.wg = some (peerUpdatedDevice d pid p now)) := by
  intro w ret v hd hr
  cases resident : d.peers[pid]? with
  | none => exact False.elim (keyPeer_missing pid w ret v (by simp [peerAt, hd, resident]) hr)
  | some p =>
    obtain ⟨now, hv⟩ := keyPeer_quiet_exact pid d p resident w ret v hd hr
    exact ⟨p, now, rfl, hv⟩

/-- Ordered peer-list effects when staged sending is disabled. Each step
requires an actual resident peer; repeated peers and keypair aliases are allowed.
The clock values are existential here; the per-operation clock relation is in
ExpiryClock. -/
inductive KeyPeerUpdates : Device → List PeerId → Device → Prop
  | nil (d : Device) : KeyPeerUpdates d [] d
  | cons (d : Device) (pid : PeerId) (p : Peer) (now : Int64) (rest : List PeerId) (final : Device)
      (resident : d.peers[pid]? = some p)
      (tail : KeyPeerUpdates (peerUpdatedDevice d pid p now) rest final) :
      KeyPeerUpdates d (pid :: rest) final

theorem keyPeerLoop_quiet (pids : List PeerId) (d : Device) :
    Ensures (keyPeerLoopSource pids false) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ KeyPeerUpdates d pids final) := by
  induction pids generalizing d with
  | nil =>
    intro w ret v hp hr
    simp [keyPeerLoopSource, StateT.run] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨d, hp, .nil d⟩
  | cons pid rest ih =>
    have factor : keyPeerLoopSource (pid :: rest) false = ((do
        _ ← branch .setDevKeyPeerIter true
        keyPeerSource pid false) >>= fun _ => keyPeerLoopSource rest false) := by
      simp [keyPeerLoopSource, List.forIn_cons, bind_assoc]
    have hstep : Ensures (do
        _ ← branch .setDevKeyPeerIter true
        keyPeerSource pid false) (fun w => w.k.wg = some d)
        (fun _ w => ∃ p now, d.peers[pid]? = some p ∧ w.k.wg = some (peerUpdatedDevice d pid p now)) := by
      have hs := (ensures_iff _ _ _).mp (keyPeer_quiet_step pid d)
      rw [ensures_iff]
      mvcgen [branch, hs]
    rw [factor]
    refine ensures_bind (R := fun (_ : Unit) w => ∃ final, w.k.wg = some final ∧ KeyPeerUpdates d (pid :: rest) final)
      _ _ hstep ?_
    intro _ w ret v hp hr
    obtain ⟨p, now, resident, hd⟩ := hp
    obtain ⟨final, hv, tail⟩ := ih (peerUpdatedDevice d pid p now) w ret v hd hr
    exact ⟨final, hv, .cons d pid p now rest final resident tail⟩

def keyInstallSource (key : Key) : M Unit := do
  let d ← getDev
  let sendStaged ← WG.andM (branch .setDevSendStagedNoIdentity !d.staticIdentity.hasIdentity)
    (branch .setDevSendStagedRunning d.running)
  setStaticIdentityPrivateKey key
  let hasIdentity := (← getDev).staticIdentity.hasIdentity
  let sendStaged ← WG.andM (branch .setDevSendStagedKept sendStaged) (branch .setDevSendStagedHasIdentity hasIdentity)
  cookiePrecomputeDeviceKeys
  keyPeerLoopSource (← getDev).peerList sendStaged
  _ ← branch .setDevKeyPeerIter false

def deviceKeyFactoredSource (a : DeviceAttrs) : M Int := do
  if ← WG.andM (branch .setDevHasPrivateKey a.privateKey.isSome) (branch .setDevPrivateKeyLen true) then
    let some key := a.privateKey | invariant "unreachable"
    -- `!crypto_memneq(static_private, private_key)`: the stored key is clamped
    if !(← branch .setDevKeyUnchanged ((← getDev).staticIdentity.staticPrivate == key)) then
      -- remove the peer whose public key the device is about to take
      let (pub, ok) ← generatePublic key
      if ← branch .setDevGenPublic ok then
        let some pub := pub | invariant "a generated public key without a write"
        let peer ← pubkeyLookup pub
        if ← branch .setDevOldPeer peer.isSome then
          peerPut peer
          peerRemove peer
      keyInstallSource key
  devicePeersSource a


theorem deviceKey_loop_factor (a : DeviceAttrs) :
    deviceKeyFactoredSource a = deviceKeySource a := by
  have map_cond (b : Bool) (act : M Unit) :
      ((fun (_ : Unit) => ForInStep.yield PUnit.unit) <$> (if b then act else pure ())) =
      (if b then (fun (_ : Unit) => ForInStep.yield PUnit.unit) <$> act else pure (ForInStep.yield PUnit.unit)) := by
    cases b <;> simp
  simp [deviceKeyFactoredSource, keyInstallSource, deviceKeySource, keyPeerLoopSource, keyPeerSource, bind_assoc, map_cond]
  rfl

end Leanux.Proofs.WG.Config
