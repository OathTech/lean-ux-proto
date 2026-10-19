import Leanux.Proofs.WG.Queues.DeviceBoundary
import Leanux.Proofs.WG.Origins.JointOwnerDevice
import Leanux.Proofs.WG.Queues.HolderDeviceStop

/-! Actual device-configuration leaves retain complete funding, structural
coherence and configured identity at the same normal native endpoint. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DeviceStages
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders Configuration DeviceBoundary

private def fields (w : WGWorld) :=
  (HolderEncrypt.fields w,BaseCoherence.view w,ConfiguredIdentity.view w)

private theorem fields_keeps (same : fields v=fields w) (hi : Entry cs loans w) : Entry cs loans v :=
  ⟨HolderEncrypt.boundary_fields hi.1 (congrArg Prod.fst same),
    BaseCoherence.transport hi.2.1 (congrArg (fun s => s.2.1) same),
    fun s hs => hi.2.2 s ((congrArg (fun s => s.2.2) same).symm.trans hs)⟩

private theorem frame {action : WG.M α} (same : SameView fields action) :
    Preserves (Entry cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact fields_keeps ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run) hi

private theorem join {action : WG.M α}
    (account : Preserves (Boundary cs loans) action)
    (coherent : Preserves BaseCoherence.Inv action)
    (configured : Preserves ConfiguredIdentity.Inv action) : Preserves (Entry cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp account w a result v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp coherent w a result v b hi.2.1 run,
    (hoare_iff_run_ambient _ _ _).mp configured w a result v b hi.2.2 run⟩

private theorem base_frame {action : WG.M α} (same : SameView BaseCoherence.view action) :
    Preserves BaseCoherence.Inv action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact BaseCoherence.transport hi ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)

private theorem store {action : WG.M α} (same : SameWGStore action) :
    Preserves (Entry cs loans) action :=
  frame (same.of_factor (fun s : WGStoreView => fields {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8}) _ (fun _ => rfl))

private theorem configuration {action : WG.M α} (same : SameConfiguration action) :
    Preserves (Entry cs loans) action := by
  apply frame
  apply same.of_factor (fun s : WGOwnedView => fields {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8})
  intro w
  unfold fields HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  unfold BaseCoherence.view BaseCoherence.slots BaseCoherence.rows ConfiguredIdentity.view ConfiguredIdentity.state
  cases hd:w.dev <;> simp [configurationView,configurationDevice,wgOwnedView,wgStoreView,hd,rxView]

private theorem socket {action : WG.M α} (same : SameSocket action) :
    Preserves (Entry cs loans) action := by
  apply frame
  apply same.of_factor (fun s : WGOwnedView => fields {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8})
  intro w
  unfold fields HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  unfold BaseCoherence.view BaseCoherence.slots BaseCoherence.rows ConfiguredIdentity.view ConfiguredIdentity.state
  cases hd:w.dev <;> simp [socketView,socketDevice,wgOwnedView,wgStoreView,hd,rxView]

private theorem readPeer (pid : PeerId) : Preserves (Entry cs loans) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  exact (getPeer_normal pid w v p a b run).1 ▸ hi

private theorem modifyDevice (f : Device → Device)
    (same : ∀ w, fields {w with dev:=w.dev.map f}=fields w) :
    Preserves (Entry cs loans) (modifyDev f) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases run
  exact fields_keeps (same w) hi

private theorem modifyPeer (pid : PeerId) (f : Peer → Peer)
    (stamp : ∀ p,(f p).internalId=p.internalId) (count : ∀ p,(f p).refcount=p.refcount)
    (rx : ∀ p,(f p).rxQueue=p.rxQueue) (napi : ∀ p,(f p).napiScheduled=p.napiScheduled)
    (current : ∀ p k,(f p).keypairCurrent=some k → p.keypairCurrent=some k)
    (tx : ∀ p,(f p).txQueue.all=p.txQueue.all)
    (identity : ∀ p,ConfiguredIdentity.cell (f p)=ConfiguredIdentity.cell p) :
    Preserves (Entry cs loans) (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply join
  · exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.modify_boundary)
      pid f stamp count rx napi current tx
  · apply base_frame
    exact ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_read) pid).bind
      (fun p => (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceRemoval.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.structural_write) pid (f p))
  · exact ConfiguredRemoval.frame (ConfiguredIdentity.modifyPeer_view pid f identity)

private theorem modifyPeerThen (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (stamp : ∀ p,(f p).internalId=p.internalId) (count : ∀ p,(f p).refcount=p.refcount)
    (rx : ∀ p,(f p).rxQueue=p.rxQueue) (napi : ∀ p,(f p).napiScheduled=p.napiScheduled)
    (current : ∀ p k,(f p).keypairCurrent=some k → p.keypairCurrent=some k)
    (tx : ∀ p,(f p).txQueue.all=p.txQueue.all)
    (identity : ∀ p,ConfiguredIdentity.cell (f p)=ConfiguredIdentity.cell p)
    (next : ∀ x, Preserves (Entry cs loans) (tail x)) :
    Preserves (Entry cs loans) (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (modifyPeer pid f stamp count rx napi current tx identity) next

macro "device_entry_step" : tactic => `(tactic| first
  | (receive_update_head setPeer
     apply modifyPeer
     all_goals first | (intro p; rfl) | (intro p k h; exact h))
  | (receive_update_head Bind.bind
     apply modifyPeerThen
     all_goals first | (intro p; rfl) | (intro p k h; exact h) | skip
     intro x)
  | (rx_retention_head getPeer; exact readPeer _)
  | (rx_retention_head getDev; exact store getDev_sameWGStore)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head modifyDev
     apply modifyDevice
     intro w
     unfold fields HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
     unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
     unfold BaseCoherence.view BaseCoherence.slots BaseCoherence.rows ConfiguredIdentity.view ConfiguredIdentity.state
     cases hd:w.dev <;> simp [hd,rxView])
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Entry _ _)
     intro x b
     change Preserves (Entry _ _) _)
  | rx_retention_step)

/-- Exact source endpoint/cache reset retains every account component. -/
theorem clearEndpoint (pid : PeerId) : Preserves (Entry cs loans) (clearPeerEndpointSrc pid) := by
  unfold clearPeerEndpointSrc dstCacheResetNow dstCacheReset
  simp (config := {zeta := false}) only [getAmbient,hiddenJiffies]
  repeat' device_entry_step

/-- Both inactive assignment and live socket replacement retain the account. -/
theorem port (port : Nat) : Preserves (Entry cs loans) (setPort port) := by
  unfold setPort
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head clearPeerEndpointSrc; exact clearEndpoint _)
    | (rx_retention_head socketInit; exact socket (socketInit_sameSocket _))
    | device_entry_step

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
  obtain ⟨holders,funded,stable⟩ := hi.1
  refine ⟨⟨holders,⟨funded.aligned.frame passive,funded.carriers.view (congrArg Prod.fst kept.1)⟩,
    stable.view (congrArg Prod.snd kept.1)⟩,?_,?_⟩
  · apply BaseCoherence.transport hi.2.1
    apply Prod.ext
    · exact congrArg (fun x : Option (List PeerId) => x.getD []) kept.2
    · exact (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherence.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.rows_of_configured) identity
  · intro st hs
    exact hi.2.2 st (identity.symm.trans hs)

theorem staged (pid : PeerId) : Preserves (Entry cs loans) (sendStagedPackets pid) :=
  join (HolderTimers.staged_boundary pid) (base_frame (BaseCoherence.staged_view pid))
    (ConfiguredTraffic.staged pid)


private theorem handshake (pid : PeerId) : Preserves (Entry cs loans) (handshakeClear pid) :=
  join (HolderDeviceStop.handshake pid) (base_frame (BaseCoherence.handshakeClear_view pid))
    (ConfiguredRemoval.frame (ConfiguredMaintenance.handshakeClear_view pid))

private theorem reset (pid : PeerId) : Preserves (Entry cs loans) (resetLastSentHandshake pid) := by
  apply join (HolderDeviceStop.reset pid)
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


macro "device_source_step" : tactic => `(tactic| first
  | (env_bind_head pubkeyLookup; exact DeviceBoundary.keyConflict_entry _)
  | (rx_retention_head devicePeersSource; exact DeviceBoundary.peers _)
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp (Entry _ _))
  | (rx_retention_head setStaticIdentityPrivateKey; exact configuration (setStaticIdentityPrivateKey_sameConfiguration _))
  | (rx_retention_head cookiePrecomputeDeviceKeys; exact configuration cookiePrecomputeDeviceKeys_sameConfiguration)
  | (rx_retention_head precomputeStaticStatic; exact precompute _)
  | (rx_retention_head expireCurrentPeerKeypairs; exact expire _)
  | (rx_retention_head sendStagedPackets; exact staged _)
  | (rx_retention_head clearPeerEndpointSrc; exact clearEndpoint _)
  | (rx_retention_head setPort; exact port _)
  | (rx_retention_head peerRemoveAll; exact DeviceBoundary.removeAll_entry)
  | device_entry_step)

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
  repeat' device_source_step

private theorem keyChanged_keeps (key : Key) : Preserves (Entry cs loans) (keyChanged key) := by
  unfold keyChanged
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head keyFinish; exact keyFinish_keeps _)
    | (rx_retention_head keyConflict; exact DeviceBoundary.keyConflict_entry _)
    | device_source_step

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
    | device_source_step

theorem update (attrs : DeviceAttrs) (flags : UInt32) :
    Preserves (Entry cs loans) (deviceUpdateSource attrs flags) := by
  unfold deviceUpdateSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head deviceKeySource; exact key _)
    | device_source_step

/-- The original complete device command preserves its supplied complete
account and registry on every normal success or errno return. -/
theorem device (attrs : DeviceAttrs) : Preserves (Entry cs loans) (wgSetDevice attrs) := by
  rw [←wgSetDevice_source]
  unfold wgSetDeviceSource WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (Entry _ _))
    | (rx_retention_head deviceUpdateSource; exact update _ _)
    | device_source_step

end Leanux.Proofs.WG.Queues.RxCredits.DeviceStages
