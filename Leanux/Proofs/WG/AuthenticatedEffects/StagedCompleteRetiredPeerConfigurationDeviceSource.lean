import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerConfigurationDeviceFrames

/-! The real device command preserves one exact reference account through
private-key changes, key invalidation, all peer commands and bulk removal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.ConfigurationDevice
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders Configuration ConfigurationDeviceBoundary

theorem handshake_account (pid : PeerId) : Preserves (ExactBoundary cs loans) (handshakeClear pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  rintro w a result v b ⟨holders,account⟩ run
  cases result
  exact ⟨holders,account.handshake_clear run⟩

theorem reset_account (pid : PeerId) : Preserves (ExactBoundary cs loans) (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshake
  simp only [hiddenClock64]
  repeat' first
    | (receive_update_head setPeer
       apply TimerFrames.modify_boundary
       all_goals first | (intro p; rfl) | (intro p kid h; exact h))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

/-- Exact source endpoint/cache reset retains every account component. -/
theorem clearEndpoint (pid : PeerId) : Preserves (Entry cs loans) (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc dstCacheResetNow dstCacheReset
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' retired_device_entry_step

/-- Both inactive assignment and live socket replacement retain the account. -/
theorem port (port : Nat) : Preserves (Entry cs loans) (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact clearEndpoint _)
    | (rx_retention_head socketInit; exact socket (socketInit_sameSocket _))
    | retired_device_entry_step

/-- Reuse the established source frame for the saved static-static setter. -/
theorem precompute (pid : PeerId) : Preserves (Entry cs loans) (precomputeStaticStatic pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have raw := (ProjectedAction.iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCreation.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCreation.precompute_fields) pid)
    w a result v b run
  have kept := (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCreation.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCreation.fields_transport) raw
  have passive := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderCreation.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderCreation.precompute_frame) pid w)
    w a result v b (Frame.refl w) run
  have identity := (ProjectedAction.iff_run_ambient _ _ _).mp (ConfiguredIdentity.precompute pid)
    w a result v b run
  obtain ⟨holders,account⟩ := hi.1
  refine ⟨⟨holders,⟨account.funded.aligned.frame passive,account.funded.carriers.view (congrArg Prod.fst kept.1)⟩,
    account.upper.peer_view (congrArg (fun s => s.1.1) kept.1),
    account.stable.view (congrArg Prod.snd kept.1)⟩,?_,?_⟩
  · apply BaseCoherence.transport hi.2.1
    apply Prod.ext
    · exact congrArg (fun x : Option (List PeerId) => x.getD []) kept.2
    · exact (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherence.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.rows_of_configured) identity
  · intro st hs
    exact hi.2.2 st (identity.symm.trans hs)

theorem staged (pid : PeerId) : Preserves (Entry cs loans) (sendStagedPackets pid) :=
  join (ExactBoundary.staged pid) (base_frame (BaseCoherence.staged_view pid))
    (ConfiguredTraffic.staged pid)


private theorem handshake (pid : PeerId) : Preserves (Entry cs loans) (handshakeClear pid) :=
  join (handshake_account pid) (base_frame (BaseCoherence.handshakeClear_view pid))
    (ConfiguredRemoval.frame (ConfiguredMaintenance.handshakeClear_view pid))

private theorem reset (pid : PeerId) : Preserves (Entry cs loans) (resetLastSentHandshake pid) := by
  apply join (reset_account pid)
  · apply base_frame
    exact (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.combined_frame)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderCreation.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderCreation.resetLast_frame) pid)
      (ConfiguredIdentity.resetHandshake pid)
  · exact ConfiguredRemoval.frame (ConfiguredIdentity.resetHandshake pid)

private theorem invalidate (kid : KeypairId) : Preserves (Entry cs loans) (do
    let k ← getKeypair kid
    setKeypair kid {k with sending := {k.sending with isValid := false}}) := by
  apply frame
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨k,read,mid,getter,write⟩ := run
  obtain ⟨readEq,timeEq,d,hd,hk⟩ := KeyTimes.getKeypair_return kid w read k a mid getter
  subst read
  subst mid
  cases write
  let changed : Keypair := {k with sending := {k.sending with isValid := false}}
  have words : keyWords {w with dev:=some {d with keypairs:=d.keypairs.insert kid changed}}=keyWords w := by
    funext q
    by_cases same:kid=q
    · subst q; simp [keyWords,hd,hk,changed]
    · simp [keyWords,hd,Std.TreeMap.getElem?_insert,same]
  change fields {w with dev:=w.dev.map (fun d => {d with keypairs:=d.keypairs.insert kid changed})}=fields w
  simp only [hd,Option.map_some]
  unfold fields HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView currentCells handoffTxView
  unfold BaseCoherence.view BaseCoherence.slots BaseCoherence.rows ConfiguredIdentity.view ConfiguredIdentity.state
  simp only [peerView,rxView,stableView,RxRing.nativeCell,passiveView,sendView,hd,
    Option.map_some,Option.bind_some,words]

/-- Expiration invalidates only sending keys and retains all charged holders. -/
theorem expire (pid : PeerId) : Preserves (Entry cs loans) (expireCurrentPeerKeypairs pid) := by
  let clear (kp : KeypairId) : WG.M Unit := do
    let k ← getKeypair kp
    setKeypair kp {k with sending := {k.sending with isValid := false}}
  let selected (decision : Decision) (slot : Option KeypairId) : WG.M Unit := do
    if ← branch decision slot.isSome then
      let some kp := slot | invariant "unreachable"
      clear kp
  have selected_keeps (decision : Decision) (slot : Option KeypairId) :
      Preserves (Entry cs loans) (selected decision slot) := by
    unfold selected
    apply preserves_bind (hoare_liftAmbient (AmbientM.branch decision slot.isSome) (Entry cs loans))
    intro present
    cases present with
    | false => exact preserves_pure ()
    | true =>
      cases slot with
      | none => exact hoare_liftAmbient (AmbientM.invariant "unreachable") (Entry cs loans)
      | some kp => exact invalidate kp
  have bind_congr {α β : Type} (a : WG.M α) (f g : α → WG.M β)
      (same : ∀ x,f x=g x) : (a >>= f)=(a >>= g) := congrArg (fun k => a >>= k) (funext same)
  have factor : expireCurrentPeerKeypairs pid=(do
      requireNotPending pid "clearing the handshake"
      handshakeClear pid
      resetLastSentHandshake pid
      let p ← getPeer pid
      selected .expireNextKeypair p.keypairNext
      selected .expireCurrentKeypair p.keypairCurrent) := by
    simp only [expireCurrentPeerKeypairs,selected,clear,requireNotPending,pure_bind]
    apply bind_congr
    intro _
    apply bind_congr
    intro _
    apply bind_congr
    intro p
    simp only [bind_assoc]
    apply bind_congr
    intro present
    cases present <;> cases p.keypairNext <;> cases p.keypairCurrent
    all_goals dsimp only
    all_goals try simp only [↓reduceIte]
    all_goals first | rfl | (symm; exact bind_assoc _ _ _) | (rw [pure_bind]; rfl)
  rw [factor]
  simp only [requireNotPending,pure_bind]
  exact preserves_bind (handshake pid) (fun _ => preserves_bind (reset pid) (fun _ =>
    preserves_bind (readPeer pid) (fun p => preserves_bind (selected_keeps .expireNextKeypair p.keypairNext)
      (fun _ => selected_keeps .expireCurrentKeypair p.keypairCurrent))))


macro "retired_device_source_step" : tactic => `(tactic| first
  | (env_bind_head pubkeyLookup; exact ConfigurationDeviceBoundary.keyConflict_entry _)
  | (rx_retention_head devicePeersSource; exact ConfigurationDeviceBoundary.peers _)
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (Entry _ _))
  | (rx_retention_head setStaticIdentityPrivateKey; exact configuration (setStaticIdentityPrivateKey_sameConfiguration _))
  | (rx_retention_head cookiePrecomputeDeviceKeys; exact configuration cookiePrecomputeDeviceKeys_sameConfiguration)
  | (rx_retention_head precomputeStaticStatic; exact precompute _)
  | (rx_retention_head expireCurrentPeerKeypairs; exact expire _)
  | (rx_retention_head sendStagedPackets; exact staged _)
  | (rx_retention_head clearPeerEndpointSrc; exact clearEndpoint _)
  | (rx_retention_head setPort; exact port _)
  | (rx_retention_head peerRemoveAll; exact ConfigurationDeviceBoundary.removeAll_entry)
  | retired_device_entry_step)

private def keyFinish (key : Key) : WG.M Unit := do
  let d ← getDev
  let sendStaged ← WG.andM (branch .setDevSendStagedNoIdentity !d.staticIdentity.hasIdentity)
    (branch .setDevSendStagedRunning d.running)
  setStaticIdentityPrivateKey key
  let hasIdentity := (← getDev).staticIdentity.hasIdentity
  let sendStaged ← WG.andM (branch .setDevSendStagedKept sendStaged) (branch .setDevSendStagedHasIdentity hasIdentity)
  cookiePrecomputeDeviceKeys
  for pid in (← getDev).peerList do
    _ ← branch .setDevKeyPeerIter true
    precomputeStaticStatic pid
    expireCurrentPeerKeypairs pid
    if ← branch .setDevSendStagedPeer sendStaged then sendStagedPackets pid
  _ ← branch .setDevKeyPeerIter false

private def keyConflict (key : Key) : WG.M Unit := do
  let peer ← pubkeyLookup key
  if ← branch .setDevOldPeer peer.isSome then
    peerPut peer
    peerRemove peer

private def keyChanged (key : Key) : WG.M Unit := do
  let (pub, ok) ← generatePublic key
  if ← branch .setDevGenPublic ok then
    let some pub := pub | invariant "a generated public key without a write"
    keyConflict pub
  keyFinish key

private theorem keyFinish_keeps (key : Key) : Preserves (Entry cs loans) (keyFinish key) := by
  unfold keyFinish WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' retired_device_source_step

private theorem keyChanged_keeps (key : Key) : Preserves (Entry cs loans) (keyChanged key) := by
  unfold keyChanged
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head keyFinish; exact keyFinish_keeps _)
    | (rx_retention_head keyConflict; exact ConfigurationDeviceBoundary.keyConflict_entry _)
    | retired_device_source_step

private theorem key_factor (attrs : DeviceAttrs) : deviceKeySource attrs=(do
    if ← WG.andM (branch .setDevHasPrivateKey attrs.privateKey.isSome) (branch .setDevPrivateKeyLen true) then
      let some key := attrs.privateKey | invariant "unreachable"
      if !(← branch .setDevKeyUnchanged ((← getDev).staticIdentity.staticPrivate == key)) then
        keyChanged key
    devicePeersSource attrs) := by
  have bind_congr {α β : Type} (action : WG.M α) (left right : α → WG.M β)
      (same : ∀ x,left x=right x) : (action >>= left)=(action >>= right) :=
    congrArg (fun tail => action >>= tail) (funext same)
  simp only [deviceKeySource,keyChanged,keyFinish,keyConflict,bind_assoc,
    TxDisposition.bind_ite,pure_bind]
  apply bind_congr
  intro present
  cases present with
  | false => rfl
  | true =>
    cases attrs.privateKey with
    | none => rfl
    | some key =>
      apply bind_congr
      intro d
      apply bind_congr
      intro unchanged
      cases unchanged with
      | true => rfl
      | false =>
        apply bind_congr
        rintro ⟨pub,ok⟩
        apply bind_congr
        intro generated
        cases generated with
        | false => rfl
        | true =>
          cases pub with
          | none => simp only [bind_assoc,pure_bind]
          | some pub => simp only [bind_assoc,TxDisposition.bind_ite,pure_bind]

/-- The complete private-key and peer-list continuation keeps one account,
including conflict removal, key expiry and newly funded staged sends. -/
theorem key (attrs : DeviceAttrs) : Preserves (Entry cs loans) (deviceKeySource attrs) := by
  rw [key_factor]
  unfold WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head keyChanged; exact keyChanged_keeps _)
    | retired_device_source_step

theorem update (attrs : DeviceAttrs) (flags : UInt32) :
    Preserves (Entry cs loans) (deviceUpdateSource attrs flags) := by
  unfold deviceUpdateSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head deviceKeySource; exact key _)
    | retired_device_source_step

/-- The original complete device command preserves its supplied complete
account and registry on every normal success or errno return. -/
theorem device (attrs : DeviceAttrs) : Preserves (Entry cs loans) (wgSetDevice attrs) := by
  rw [←wgSetDevice_source]
  unfold wgSetDeviceSource WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (Entry _ _))
    | (rx_retention_head deviceUpdateSource; exact update _ _)
    | retired_device_source_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.ConfigurationDevice
