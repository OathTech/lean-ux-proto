import Leanux.Proofs.WG.Config.ExpiryClock

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Original peer update with only its curve-bearing precomputation exposed. -/
def keyPeerSourceWith (precompute : PeerId → WG.M Unit)
    (pid : PeerId) (sendStaged : Bool) : WG.M Unit := do
  precompute pid
  expireCurrentPeerKeypairs pid
  if ← branch .setDevSendStagedPeer sendStaged then sendStagedPackets pid

def keyPeerSource (pid : PeerId) (sendStaged : Bool) : WG.M Unit :=
  keyPeerSourceWith precomputeStaticStatic pid sendStaged

/-- The saved peer-list traversal with its actual precomputation callback. -/
def keyPeerLoopSourceWith (precompute : PeerId → WG.M Unit)
    (pids : List PeerId) (sendStaged : Bool) : WG.M Unit := do
  for pid in pids do
    _ ← branch .setDevKeyPeerIter true
    keyPeerSourceWith precompute pid sendStaged

def keyPeerLoopSource (pids : List PeerId) (sendStaged : Bool) : WG.M Unit :=
  keyPeerLoopSourceWith precomputeStaticStatic pids sendStaged

def peerUpdatedDevice (d : Device) (pid : PeerId) (p : Peer) (now : Int64) : Device :=
  expiredDevice (precomputeDevice d pid p) pid
    { p with precomputedStaticStatic := precomputedAfter d.staticIdentity p } now

theorem keyPeer_quiet_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (keyPeerSource pid false) (fun w => w.dev = some d)
      (fun _ w => ∃ now, w.dev = some (peerUpdatedDevice d pid p now)) := by
  have hp : Ensures (precomputeStaticStatic pid) (fun g => g.dev = some d)
      (fun _ g => g.dev = some (precomputeDevice d pid p)) := by
    intro g ambient result final after device run
    obtain ⟨u, out, tail, execution, post⟩ :=
      precomputeStaticStatic_returns pid d p resident g ambient device
    rw [run] at execution
    cases execution
    exact post
  have he := expireCurrent_exact pid (precomputeDevice d pid p)
    {p with precomputedStaticStatic := precomputedAfter d.staticIdentity p}
    (precomputeDevice_peer pid d p)
  unfold keyPeerSource keyPeerSourceWith
  refine ensures_bind _ _ hp ?_
  intro _
  refine ensures_bind _ _ he ?_
  intro _ g ambient result final after pre run
  simp [branch, AmbientM.branch] at run
  rcases run with ⟨rfl, rfl⟩
  exact pre

theorem keyPeer_missing (pid : PeerId) :
    Ensures (keyPeerSource pid false) (fun w => peerAt w pid = none) (fun _ _ => False) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [keyPeerSource, keyPeerSourceWith, precomputeStaticStatic, requireNotPending, getDev, device,
      invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    have missing : d.peers[pid]? = none := by simpa [peerAt, device] using pre
    simp [keyPeerSource, keyPeerSourceWith, precomputeStaticStatic, requireNotPending, getPeer, getDev, device,
      missing, invariant, AmbientM.invariant] at run
    cases run

theorem keyPeer_quiet_step (pid : PeerId) (d : Device) :
    Ensures (keyPeerSource pid false) (fun w => w.dev = some d)
      (fun _ w => ∃ p now, d.peers[pid]? = some p ∧ w.dev = some (peerUpdatedDevice d pid p now)) := by
  intro w ambient ret v after hd hr
  cases resident : d.peers[pid]? with
  | none =>
    exact False.elim (keyPeer_missing pid w ambient ret v after
      (by simp [peerAt, hd, resident]) hr)
  | some p =>
    obtain ⟨now, hv⟩ := keyPeer_quiet_exact pid d p resident w ambient ret v after hd hr
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
    Ensures (keyPeerLoopSource pids false) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧ KeyPeerUpdates d pids final) := by
  induction pids generalizing d with
  | nil =>
    intro w ambient ret v after hp hr
    simp [keyPeerLoopSource, keyPeerLoopSourceWith] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact ⟨d, hp, .nil d⟩
  | cons pid rest ih =>
    have factor : keyPeerLoopSource (pid :: rest) false = ((do
        _ ← branch .setDevKeyPeerIter true
        keyPeerSource pid false) >>= fun _ => keyPeerLoopSource rest false) := by
      simp [keyPeerLoopSource, keyPeerLoopSourceWith, keyPeerSource, List.forIn_cons, bind_assoc]
    have hstep : Ensures (do
        _ ← branch .setDevKeyPeerIter true
        keyPeerSource pid false) (fun w => w.dev = some d)
        (fun _ w => ∃ p now, d.peers[pid]? = some p ∧ w.dev = some (peerUpdatedDevice d pid p now)) := by
      refine ensures_bind _ _
        ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
          (AmbientM.branch .setDevKeyPeerIter true) (fun g : WGWorld => g.dev = some d))) ?_
      intro _
      exact keyPeer_quiet_step pid d
    rw [factor]
    refine ensures_bind (R := fun (_ : Unit) w => ∃ final, w.dev = some final ∧ KeyPeerUpdates d (pid :: rest) final)
      _ _ hstep ?_
    intro _ w ambient ret v after hp hr
    obtain ⟨p, now, resident, hd⟩ := hp
    obtain ⟨final, hv, tail⟩ := ih (peerUpdatedDevice d pid p now) w ambient ret v after hd hr
    exact ⟨final, hv, .cons d pid p now rest final resident tail⟩

/-- Original installation with identity and precomputation callbacks exposed. -/
def keyInstallSourceWith (setPrivate : Key → WG.M Unit)
    (precompute : PeerId → WG.M Unit) (key : Key) : WG.M Unit := do
  let d ← getDev
  let sendStaged ← WG.andM (branch .setDevSendStagedNoIdentity !d.staticIdentity.hasIdentity)
    (branch .setDevSendStagedRunning d.running)
  setPrivate key
  let hasIdentity := (← getDev).staticIdentity.hasIdentity
  let sendStaged ← WG.andM (branch .setDevSendStagedKept sendStaged) (branch .setDevSendStagedHasIdentity hasIdentity)
  cookiePrecomputeDeviceKeys
  keyPeerLoopSourceWith precompute (← getDev).peerList sendStaged
  _ ← branch .setDevKeyPeerIter false

def keyInstallSource (key : Key) : WG.M Unit :=
  keyInstallSourceWith setStaticIdentityPrivateKey precomputeStaticStatic key

def deviceKeyFactoredSource (a : DeviceAttrs) : WG.M Int := do
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
  have map_cond (b : Bool) (act : WG.M Unit) :
      ((fun (_ : Unit) => ForInStep.yield PUnit.unit) <$> (if b then act else pure ())) =
      (if b then (fun (_ : Unit) => ForInStep.yield PUnit.unit) <$> act else pure (ForInStep.yield PUnit.unit)) := by
    cases b <;> simp
  simp [deviceKeyFactoredSource, keyInstallSource, keyInstallSourceWith, deviceKeySource, keyPeerLoopSourceWith, keyPeerSourceWith, bind_assoc, map_cond]
  rfl

end Leanux.Proofs.WG.Config
