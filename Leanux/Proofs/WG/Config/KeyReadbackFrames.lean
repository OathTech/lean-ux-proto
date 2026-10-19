import Leanux.Proofs.WG.Config.KeyReadbackModel
import Leanux.Proofs.WG.Config.KeyRequest
import Leanux.Proofs.WG.Config.ScalarGetterSource

/-! Substantive native socket/selector and within-Device rotation frames. -/

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

/-- Socket and selector preservation across actual precomputation, handshake
removal, clock consumption and both key invalidations. Device effects are not
used to infer preservation of these other WireGuard fields. -/
theorem keyPeer_quiet_readbackFrame (pid : PeerId) (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (keyPeerSource pid false) (fun g => readbackFrame g sock fixtures)
      (fun _ g => readbackFrame g sock fixtures) := by
  let P : WGWorld → Prop := fun g => readbackFrame g sock fixtures
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g ambient value final after pre run
    cases run
    exact pre
  have hbranch (site : Decision) (value : Bool) : Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hdev : Ensures getDev P (fun _ => P) := by
    intro g ambient value final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hpeer : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient value final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P) g ambient value final after pre run).1
  have hmodify (f : Device → Device) : Ensures (modifyDev f) P (fun _ => P) := by
    intro g ambient value final after pre run
    cases run
    exact pre
  have hset (p : Peer) : Ensures (setPeer pid p) P (fun _ => P) := hmodify _
  have hkey (id : KeypairId) : Ensures (getKeypair id) P (fun _ => P) := by
    intro g ambient value final after pre run
    cases device : g.dev with
    | none => simp [getKeypair, getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      cases found : d.keypairs[id]? with
      | none => simp [getKeypair, getDev, device, found, invariant, AmbientM.invariant] at run; cases run
      | some k =>
        simp [getKeypair, getDev, device, found] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        exact pre
  have precompute : Ensures (precomputeStaticStatic pid) P (fun _ => P) := by
    unfold precomputeStaticStatic
    simp only [requireNotPending, pure_bind]
    refine ensures_bind (Q := fun _ => P) _ _ hdev ?_
    intro d
    refine ensures_bind (Q := fun _ => P) _ _ hpeer ?_
    intro p
    refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
    intro noIdentity
    cases noIdentity with
    | true =>
      simp only [↓reduceIte]
      exact ensures_bind _ _ hpeer (fun p => hset _)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ensures_bind (Q := fun _ => P) _ _ (hset _) ?_
      intro _
      refine ensures_bind (Q := fun _ => P) _ _ (hbranch _ _) ?_
      intro zero
      cases zero with
      | false => exact hpure ()
      | true => exact ensures_bind _ _ hpeer (fun p => hset _)
  have clear : Ensures (handshakeClear pid) P (fun _ => P) := by
    have deref : Ensures (IndexOwner.peerDeref (.handshake pid)) P (fun _ => P) := by
      unfold IndexOwner.peerDeref IndexOwner.peerWord
      refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
      · exact ensures_bind _ _ hpeer (fun p => hpure p.handshakeEntryPeer)
      · intro word
        cases word with
        | none => exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
            (AmbientM.unsupported "entry->peer is NULL: the C dereferences it") P)
        | some owner => exact hpure owner
    have remove : Ensures (liftIndex (indexRemove (.handshake pid))) P (fun _ => P) := by
      exact (ensures_iff _ _ _).mpr (hoare_liftIndex_variant _ P (by intro g d table pre device; exact pre))
    unfold handshakeClear
    refine ensures_bind _ _ deref (fun _ => ensures_bind _ _ remove ?_)
    intro _
    unfold handshakeZero
    exact ensures_bind _ _ hpeer (fun p => hset _)
  have reset : Ensures (resetLastSentHandshake pid) P (fun _ => P) := by
    unfold resetLastSentHandshake
    refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
    · exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hiddenClock64 .resetLastSent) P)
    · intro now
      exact ensures_bind _ _ hpeer (fun p => hset _)
  have invalidate (site : Decision) (kp : Option KeypairId) : Ensures (invalidateSource site kp) P (fun _ => P) := by
    cases kp with
    | none =>
      intro g ambient value final after pre run
      simp [invalidateSource, branch, AmbientM.branch] at run
      rcases run with ⟨rfl, rfl⟩
      exact pre
    | some id =>
      have step : Ensures (do
          let k ← getKeypair id
          setKeypair id {k with sending := {k.sending with isValid := false}}) P (fun _ => P) :=
        ensures_bind _ _ (hkey id) (fun k => hmodify _)
      intro g ambient value final after pre run
      exact step g _ value final after pre
        (by simpa [invalidateSource, branch, AmbientM.branch] using run)
  have expire : Ensures (expireCurrentPeerKeypairs pid) P (fun _ => P) := by
    rw [expireCurrent_source]
    unfold expiryHeadSource expiryTailSource
    simp only [requireNotPending, pure_bind]
    refine ensures_bind _ _ (ensures_bind _ _ clear (fun _ => reset)) ?_
    intro _
    refine ensures_bind _ _ hpeer ?_
    intro p
    exact ensures_bind _ _ (invalidate .expireNextKeypair p.keypairNext)
      (fun _ => invalidate .expireCurrentKeypair p.keypairCurrent)
  unfold keyPeerSource keyPeerSourceWith
  refine ensures_bind _ _ precompute (fun _ => ensures_bind _ _ expire ?_)
  intro _ g ambient value final after pre run
  simp [branch, AmbientM.branch] at run
  rcases run with ⟨rfl, rfl⟩
  exact pre

/-- Established identity disables the staged-send branch without assuming
anything about queued work, key residency, or expiry-clock readiness. -/
theorem keyInstall_established_readbackFrame (d : Device) (key : Key)
    (sock : NlSock) (fixtures : FixtureDevices) (established : d.staticIdentity.hasIdentity = true) :
    Ensures (keyInstallSource key) (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => readbackFrame g sock fixtures) := by
  have idle (pids : List PeerId) :
      List.foldlM (fun (_ : Unit) pid => requireNotPending pid "changing the device identity") () pids =
        (pure () : WG.M Unit) := by
    induction pids with
    | nil => rfl
    | cons pid pids ih => simpa only [List.foldlM_cons, requireNotPending, pure_bind] using ih
  have identityFrame : Ensures (setStaticIdentityPrivateKey key)
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => readbackFrame g sock fixtures) := by
    intro g ambient value final after pre run
    cases null : key == nullPoint <;>
      simp [setStaticIdentityPrivateKey, idle, getDev, pre.1, generatePublic,
        branch, AmbientM.branch, null, modifyDev] at run
    all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals exact pre.2
  have cookieFrame (d : Device) : Ensures cookiePrecomputeDeviceKeys
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => readbackFrame g sock fixtures) := by
    intro g ambient value final after pre run
    cases has : d.staticIdentity.hasIdentity <;>
      simp [cookiePrecomputeDeviceKeys, getDev, pre.1, modifyDev, branch, AmbientM.branch, has] at run
    all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals exact pre.2
  have loop (pids : List PeerId) : Ensures (keyPeerLoopSource pids false)
      (fun g => readbackFrame g sock fixtures) (fun _ g => readbackFrame g sock fixtures) := by
    induction pids with
    | nil =>
      intro g ambient value final after pre run
      cases run
      exact pre
    | cons pid rest ih =>
      have factor : keyPeerLoopSource (pid :: rest) false = (do
          _ ← branch .setDevKeyPeerIter true
          keyPeerSource pid false
          keyPeerLoopSource rest false) := by
        simp [keyPeerLoopSource, keyPeerLoopSourceWith, keyPeerSource, List.forIn_cons, bind_assoc]
      rw [factor]
      refine ensures_bind (Q := fun _ g => readbackFrame g sock fixtures) _ _ ?_ ?_
      · exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
          (AmbientM.branch .setDevKeyPeerIter true) (fun g : WGWorld => readbackFrame g sock fixtures))
      · intro _
        exact ensures_bind _ _ (keyPeer_quiet_readbackFrame pid sock fixtures) (fun _ => ih)
  intro g ambient value final after pre run
  let mark (a : Ambient) (site : Decision) (value : Bool) :=
    {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
  let first := mark ambient .setDevSendStagedNoIdentity false
  obtain ⟨u, identityState, identityAmbient, identityRun, identityDevice⟩ :=
    setStaticIdentity_returns key d g first pre.1
  cases u
  have identitySaved := identityFrame g first () identityState identityAmbient pre identityRun
  let middle := mark identityAmbient .setDevSendStagedKept false
  obtain ⟨u, cookieState, cookieAmbient, cookieRun, cookieDevice⟩ :=
    cookiePrecompute_returns {d with staticIdentity := identityAfter key d.staticIdentity}
      identityState middle identityDevice
  cases u
  have cookieSaved := cookieFrame _ identityState middle () cookieState cookieAmbient
    ⟨identityDevice, identitySaved⟩ cookieRun
  have source : ((keyInstallSource key).run g).run ambient =
      (((keyPeerLoopSource d.peerList false).run cookieState).run cookieAmbient >>= fun ((_, current), tail) =>
        .ok (((), current), mark tail .setDevKeyPeerIter false)) := by
    simp [keyInstallSource, keyInstallSourceWith, WG.andM, getDev, pre.1, established, branch, AmbientM.branch]
    rw [show ((setStaticIdentityPrivateKey key).run g).run first = _ from identityRun]
    dsimp only [bind, Except.bind]
    simp [identityDevice, pure, StateT.pure, StateT.run, Except.pure]
    dsimp only [StateT.run] at cookieRun
    rw [cookieRun]
    dsimp only [bind, Except.bind]
    simp [cookieDevice, cookieKeysAfter, pure, StateT.pure, Except.pure]
    rfl
  rw [source] at run
  cases loopRun : ((keyPeerLoopSource d.peerList false).run cookieState).run cookieAmbient with
  | error stop => rw [loopRun] at run; cases run
  | ok out =>
    obtain ⟨⟨u, current⟩, inputs⟩ := out
    rw [loopRun] at run
    cases run
    exact loop d.peerList cookieState cookieAmbient u final inputs cookieSaved loopRun

/-- The outer request's selector and socket frame comes from its actual
no-collision path, including the quiet installation's native frame. -/
theorem setDevice_rotation_readbackFrame (d : Device) (key : Key)
    (sock : NlSock) (fixtures : FixtureDevices)
    (established : d.staticIdentity.hasIdentity = true)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key) :
    Ensures (wgSetDevice (privateKeyAttrs d key))
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures ∧ selectsDevice g d)
      (fun _ g => readbackFrame g sock fixtures) := by
  let updated := requestGeneration d
  have collisionFrame (base : Device) (absent : noKeyCollision base key) :
      Ensures (keyCollisionSource key) (fun g => g.dev = some base ∧ readbackFrame g sock fixtures)
        (fun _ g => readbackFrame g sock fixtures) := by
    intro g ambient value final after pre run
    by_cases isNull : key == nullPoint
    · simp [keyCollisionSource, keyCollisionSourceWith, generatePublic, branch, AmbientM.branch, isNull] at run
      rcases run with ⟨rfl, rfl⟩
      exact pre.2
    · cases valid : (curve25519 key basePoint).2 with
      | false =>
        simp [keyCollisionSource, keyCollisionSourceWith, generatePublic, branch, AmbientM.branch, isNull, valid] at run
        rcases run with ⟨rfl, rfl⟩
        exact pre.2
      | true =>
        have missing := absent (curve25519 key basePoint).1
          (by simp [publicResult, isNull]) (by simp [publicResult, isNull, valid])
        simp [keyCollisionSource, keyCollisionSourceWith, generatePublic, branch, AmbientM.branch,
          isNull, valid, pubkeyLookup, peerGetMaybeZero, getDev, pre.1, missing] at run
        rcases run with ⟨rfl, rfl⟩
        exact pre.2
  have changedFlag : (d.staticIdentity.staticPrivate == key) = false := by
    simpa only [beq_eq_false_iff_ne] using changed
  have keyTail : Ensures (devicePrivateSource (privateKeyAttrs d key))
      (fun g => g.dev = some updated ∧ readbackFrame g sock fixtures)
      (fun _ g => readbackFrame g sock fixtures) := by
    intro g ambient value final after pre run
    let logged (a : Ambient) (site : Decision) (value : Bool) :=
      {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
    let before := logged (logged (logged ambient .setDevHasPrivateKey true)
      .setDevPrivateKeyLen true) .setDevKeyUnchanged false
    have missing : noKeyCollision updated key := by simpa [updated, noKeyCollision, requestGeneration] using absent
    obtain ⟨u, current, inputs, collisionRun, currentDevice⟩ :=
      keyCollision_absent updated key missing g before pre.1
    cases u
    have saved := collisionFrame updated missing g before () current inputs pre collisionRun
    have source : ((devicePrivateSource (privateKeyAttrs d key)).run g).run ambient =
        (((keyInstallSource key).run current).run inputs >>= fun ((_, out), tail) =>
          .ok (((0 : Int), out), logged (logged tail .setDevHasPeers false) .setDevZeroKey true)) := by
      simp [devicePrivateSource, devicePrivateSourceWith, devicePeersSource, privateKeyAttrs, WG.andM, getDev,
        pre.1, updated, requestGeneration, changed, changedFlag, branch, AmbientM.branch]
      rw [collisionRun]
      rfl
    rw [source] at run
    cases installRun : ((keyInstallSource key).run current).run inputs with
    | error stop => rw [installRun] at run; cases run
    | ok out =>
      obtain ⟨⟨u, out⟩, tail⟩ := out
      rw [installRun] at run
      cases run
      exact keyInstall_established_readbackFrame updated key sock fixtures established
        current inputs u final tail ⟨currentDevice, saved⟩ installRun
  let mark (site : Decision) (value : Bool) : WG.M Unit :=
    monadLift (modify fun a : Ambient => {a with steps := a.steps.push {
      decision := site, outcome := value, netRx := a.netRxSection}} : AmbientM Unit)
  have branchSource (site : Decision) (value : Bool) :
      (branch site value : WG.M Bool) = (do mark site value; pure value) := rfl
  have hm (site : Decision) (value : Bool) (base : Device) :
      Ensures (mark site value) (fun g => g.dev = some base ∧ readbackFrame g sock fixtures)
        (fun _ g => g.dev = some base ∧ readbackFrame g sock fixtures) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hu : Ensures (modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1})
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => g.dev = some updated ∧ readbackFrame g sock fixtures) := by
    intro g ambient result final after pre run
    cases run
    exact ⟨by simp [pre.1, updated, requestGeneration], pre.2⟩
  have tail : Ensures (do
      mark .setDevLookupErr false
      mark .setDevHasFlags false
      mark .setDevBadFlags false
      mark .setDevHasPort false
      mark .setDevHasFwmark false
      modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1}
      mark .setDevFwmark false
      mark .setDevPort false
      mark .setDevReplacePeers false
      devicePrivateSource (privateKeyAttrs d key))
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => readbackFrame g sock fixtures) := by
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine ensures_bind _ _ hu (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine ensures_bind _ _ (hm _ _ updated) (fun _ => ?_)
    exact keyTail
  rw [← wgSetDevice_source]
  unfold wgSetDeviceSource
  have lookup : Ensures (lookupInterface (byIndex d))
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures ∧ selectsDevice g d)
      (fun result g => result = .ok () ∧ g.dev = some d ∧ readbackFrame g sock fixtures) := by
    intro g ambient value final after pre run
    obtain ⟨found, out, ending, actual, post⟩ :=
      (returns_iff _ _ _).mpr (lookupInterface_index_framed d sock fixtures) g ambient pre
    rw [run] at actual
    cases actual
    exact post
  refine ensures_bind _ _ lookup ?_
  intro result g ambient ret final after pre run
  obtain ⟨rfl, device, frame⟩ := pre
  apply tail g ambient ret final after ⟨device, frame⟩
  simpa [privateKeyAttrs, deviceUpdateSource, ← devicePrivate_source, WG.orM,
    branchSource, bind_assoc, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS] using run

/-- Exact quiet rotation changes only the peer, keypair and index stores
after the identity/cookie installation. Other Device fields are retained. -/
theorem keyReadbackDevice_otherFields (d : Device) (key : Key) (pid : PeerId) (p : Peer) (now : Int64) :
    {keyReadbackDevice d key pid p now with peers := {}, keypairs := {}, indexTable := []} =
      {keyReadbackBase d key with peers := {}, keypairs := {}, indexTable := []} := by
  have invalidated (base : Device) (kp : Option KeypairId) :
      {invalidateDevice base kp with peers := {}, keypairs := {}, indexTable := []} =
        {base with peers := {}, keypairs := {}, indexTable := []} := by
    cases kp with
    | none => rfl
    | some id => cases found : base.keypairs[id]? <;> simp [invalidateDevice, found]
  unfold keyReadbackDevice peerUpdatedDevice expiredDevice
  rw [invalidated, invalidated]
  cases has : (keyReadbackBase d key).staticIdentity.hasIdentity <;>
    cases nonNull : (curve25519 (keyReadbackBase d key).staticIdentity.staticPrivate p.remoteStatic).2
  all_goals simp only [expiryHeadDevice, withPeer, precomputeDevice, has, nonNull, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

end Leanux.Proofs.WG.Config
