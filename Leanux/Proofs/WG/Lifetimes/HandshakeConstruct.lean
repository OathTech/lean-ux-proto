import Leanux.Proofs.WG.Lifetimes.LookupAccess
import Leanux.Proofs.WG.Lifetimes.ReceiveMaintenance
import Leanux.Proofs.Framing.WGHandshake
import Leanux.Proofs.Framing.WGIndex

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Complete original handshake construction and MAC calls. Only explicit-input
crypto and scalar index operations are lifted. Every resolved peer read/write is
observed; all record failures retain the access prefix. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def setChainPrefix (pid : PeerId) (ck hash : List UInt8) : MixedM Unit :=
  modifyPeerKeysPrefix pid fun p => {p with chainingKey := ck, hash}

theorem setChainPrefix_erases (pid : PeerId) (ck hash : List UInt8) :
    ErasesStatePrefix (setChainPrefix pid ck hash)
      ((pinned_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck hash) :=
  modifyPeerKeysPrefix_erases pid _

theorem setChainPrefix_preserves (c : AmbientContracts I) (pid : PeerId) (ck hash : List UInt8) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (setChainPrefix pid ck hash) :=
  AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
    (fun p => {p with chainingKey := ck, hash}) (fun _ => rfl))

def createInitiationPrefix (pid : PeerId) : MixedM (Option (List UInt8)) := do
  let identity := (← liftWGPrefix getDev).staticIdentity
  if ← liftWGPrefix (branch .initNoIdentity !identity.hasIdentity) then return none
  let p ← getPeerMixed pid
  let h := noiseHash (handshakeInitHash ++ p.remoteStatic)
  setChainPrefix pid handshakeInitChainingKey h
  let secret := clamp (← liftWGPrefix (hidden .initEphemeral))
  modifyPeerKeysPrefix pid fun p => {p with ephemeralPrivate := secret}
  let (pub, ok) ← liftWGPrefix (generatePublic secret)
  if ← liftWGPrefix (branch .initNoEphemeral !ok) then return none
  let some e := pub | liftWGPrefix (invariant "unreachable")
  let (ck, h) ← liftWGPrefix (messageEphemeral false e handshakeInitChainingKey h)
  setChainPrefix pid ck h
  let es ← liftWGPrefix (mixDh true ck secret p.remoteStatic)
  if ← liftWGPrefix (branch .initEsFailed es.isNone) then return none
  let some (ck, key) := es | liftWGPrefix (invariant "unreachable")
  let encStatic := aeadEncrypt key noiseNonce identity.staticPublic h
  let h := noiseHash (h ++ encStatic)
  setChainPrefix pid ck h
  let ss ← liftWGPrefix (mixPrecomputedDh ck p.precomputedStaticStatic)
  if ← liftWGPrefix (branch .initSsFailed ss.isNone) then return none
  let some (ck, key) := ss | liftWGPrefix (invariant "unreachable")
  let timestamp := tai64n (← liftWGPrefix (hidden .tai64nNow))
  let encTime := aeadEncrypt key noiseNonce timestamp h
  let h := noiseHash (h ++ encTime)
  setChainPrefix pid ck h
  _ ← peerDerefPrefix (.handshake pid)
  let index ← liftWGPrefix (liftIndex (indexInsert (.handshake pid)))
  modifyPeerKeysPrefix pid fun p => {p with handshakeState := HANDSHAKE_CREATED_INITIATION}
  return some (le32 1 ++ le32 index ++ e ++ encStatic ++ encTime ++ List.replicate 32 0)

def createResponsePrefix (pid : PeerId) : MixedM (Option (List UInt8)) := do
  let p ← getPeerMixed pid
  if ← liftWGPrefix (branch .respNotConsumed (p.handshakeState != HANDSHAKE_CONSUMED_INITIATION)) then return none
  let receiver := p.remoteIndex
  let secret := clamp (← liftWGPrefix (hidden .respEphemeral))
  modifyPeerKeysPrefix pid fun p => {p with ephemeralPrivate := secret}
  let (pub, ok) ← liftWGPrefix (generatePublic secret)
  if ← liftWGPrefix (branch .respNoEphemeral !ok) then return none
  let some e := pub | liftWGPrefix (invariant "unreachable")
  let (ck, h) ← liftWGPrefix (messageEphemeral false e p.chainingKey p.hash)
  setChainPrefix pid ck h
  let ee ← liftWGPrefix (mixDh false ck secret p.remoteEphemeral)
  if ← liftWGPrefix (branch .respEeFailed ee.isNone) then return none
  let some (ck, _) := ee | liftWGPrefix (invariant "unreachable")
  setChainPrefix pid ck h
  let se ← liftWGPrefix (mixDh false ck secret p.remoteStatic)
  if ← liftWGPrefix (branch .respSeFailed se.isNone) then return none
  let some (ck, _) := se | liftWGPrefix (invariant "unreachable")
  let outs ← liftWGPrefix (kdf true true ck p.presharedKey)
  let (ck, tempHash, key) := (← liftWGPrefix (kdfOut outs 0), ← liftWGPrefix (kdfOut outs 1), ← liftWGPrefix (kdfOut outs 2))
  let h := noiseHash (h ++ tempHash)
  let encNothing := aeadEncrypt key noiseNonce [] h
  let h := noiseHash (h ++ encNothing)
  setChainPrefix pid ck h
  _ ← peerDerefPrefix (.handshake pid)
  let index ← liftWGPrefix (liftIndex (indexInsert (.handshake pid)))
  modifyPeerKeysPrefix pid fun p => {p with handshakeState := HANDSHAKE_CREATED_RESPONSE}
  return some (le32 2 ++ le32 index ++ le32 receiver ++ e ++ encNothing ++ List.replicate 32 0)

def addMacToPacketPrefix (pid : PeerId) (msg : List UInt8) : MixedM (List UInt8) := do
  let p ← getPeerMixed pid
  let body := msg.take (msg.length - 32)
  let mac1 := blake2s 16 p.cookieMac1Key body
  setPeerMixed pid {p with lastMac1Sent := mac1, haveSentMac1 := true}
  if ← andPrefix (liftWGPrefix (branch .addMacCookieValid p.cookieIsValid))
      (liftWGPrefix (branchExpired .addMacCookieFresh p.cookieBirthdate COOKIE_FRESH_SECONDS (!·))) then
    return body ++ mac1 ++ blake2s 16 p.cookie (body ++ mac1)
  return body ++ mac1 ++ List.replicate 16 0

theorem createInitiationPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (createInitiationPrefix pid) (createInitiation pid) := by
  unfold createInitiationPrefix createInitiation modifyPeerKeysPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact setChainPrefix_erases _ _ _
    | with_reducible exact modifyPeerKeysPrefix_erases _ _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact peerDerefPrefix_erases _
    | with_reducible exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply andPrefix_erases_state
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals try simp_all
  all_goals first | exact erasesStatePrefix_lift _ | exact erasesStatePrefix_pure _ | exact andPrefix_erases_state (erasesStatePrefix_lift _) (erasesStatePrefix_lift _)

theorem createResponsePrefix_erases (pid : PeerId) :
    ErasesStatePrefix (createResponsePrefix pid) (createResponse pid) := by
  unfold createResponsePrefix createResponse modifyPeerKeysPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact setChainPrefix_erases _ _ _
    | with_reducible exact modifyPeerKeysPrefix_erases _ _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact peerDerefPrefix_erases _
    | with_reducible exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply andPrefix_erases_state
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals try simp_all
  all_goals first | exact erasesStatePrefix_lift _ | exact erasesStatePrefix_pure _ | exact andPrefix_erases_state (erasesStatePrefix_lift _) (erasesStatePrefix_lift _)

theorem addMacToPacketPrefix_erases (pid : PeerId) (msg : List UInt8) :
    ErasesStatePrefix (addMacToPacketPrefix pid msg) (addMacToPacket pid msg) := by
  unfold addMacToPacketPrefix addMacToPacket
  repeat' first
    | with_reducible exact setChainPrefix_erases _ _ _
    | with_reducible exact modifyPeerKeysPrefix_erases _ _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact peerDerefPrefix_erases _
    | with_reducible exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply andPrefix_erases_state
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals try simp_all
  all_goals first | exact erasesStatePrefix_lift _ | exact erasesStatePrefix_pure _ | exact andPrefix_erases_state (erasesStatePrefix_lift _) (erasesStatePrefix_lift _)

theorem addMacToPacketPrefix_preserves (c : AmbientContracts I) (pid : PeerId) (msg : List UInt8) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (addMacToPacketPrefix pid msg) := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  unfold addMacToPacketPrefix
  apply StatePrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  dsimp only
  apply StatePrefixEnsures.bind (c.setPeer (fun _ => True) pid
    {p with lastMac1Sent := blake2s 16 p.cookieMac1Key (msg.take (msg.length - 32)), haveSentMac1 := true})
  intro _
  apply StatePrefixEnsures.bind
  · unfold andPrefix
    apply StatePrefixEnsures.bind (c.branch (fun _ => True) _ _)
    intro valid
    split
    · exact c.store (fun _ => True) _ ((branchExpired_sameWGWorld _ _ _ _).of_factor wgStoreView wgStoreView (fun _ => rfl))
    · exact c.pure (fun _ => True) false
  · intro fresh
    split <;> exact c.pure (fun _ => True) _


theorem createInitiationPrefix_preserves (c : AmbientContracts I)
    (hi : ∀ owner, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (liftWGPrefix (liftIndex (indexInsert owner))))
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (createInitiationPrefix pid) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix a) :=
    AmbientContracts.drop (c.store (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (StateT.lift a)) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  have whole {α : Type} (a : WG.M α) (ha : SameView (id : WGWorld → WGWorld) a) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix a) :=
    store a (ha.of_factor wgStoreView wgStoreView (fun _ => rfl))
  have dev : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix getDev) := by
    apply store
    intro initial
    unfold Hoare
    mvcgen [getDev, invariant, AmbientM.invariant]
  unfold createInitiationPrefix
  repeat' first
    | (maintenance_head setChainPrefix; exact setChainPrefix_preserves c _ _ _)
    | (maintenance_head modifyPeerKeysPrefix; exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_lift_action_head getDev; exact dev)
    | (maintenance_lift_action_head hidden; exact ambient (AmbientM.hidden _))
    | (maintenance_lift_action_head generatePublic; exact whole _ (Framing.generatePublic_sameWGWorld _))
    | (maintenance_lift_action_head messageEphemeral; exact whole _ (Framing.messageEphemeral_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head mixDh; exact whole _ (Framing.mixDh_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head mixPrecomputedDh; exact whole _ (Framing.mixPrecomputedDh_sameWGWorld _ _))
    | (maintenance_lift_action_head kdf; exact whole _ (Framing.kdf_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head kdfOut; exact whole _ (Framing.kdfOut_sameWGWorld _ _))
    | (maintenance_head peerDerefPrefix; exact AmbientContracts.drop (peerDerefPrefix_spec c (fun _ => True) _))
    | (maintenance_lift_action_head liftIndex; exact hi _)
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | with_reducible exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
    | with_reducible apply StatePrefixEnsures.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem createResponsePrefix_preserves (c : AmbientContracts I)
    (hi : ∀ owner, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (liftWGPrefix (liftIndex (indexInsert owner))))
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (createResponsePrefix pid) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix a) :=
    AmbientContracts.drop (c.store (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (StateT.lift a)) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  have whole {α : Type} (a : WG.M α) (ha : SameView (id : WGWorld → WGWorld) a) :
      StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix a) :=
    store a (ha.of_factor wgStoreView wgStoreView (fun _ => rfl))
  have dev : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix getDev) := by
    apply store
    intro initial
    unfold Hoare
    mvcgen [getDev, invariant, AmbientM.invariant]
  unfold createResponsePrefix
  repeat' first
    | (maintenance_head setChainPrefix; exact setChainPrefix_preserves c _ _ _)
    | (maintenance_head modifyPeerKeysPrefix; exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_lift_action_head getDev; exact dev)
    | (maintenance_lift_action_head hidden; exact ambient (AmbientM.hidden _))
    | (maintenance_lift_action_head generatePublic; exact whole _ (Framing.generatePublic_sameWGWorld _))
    | (maintenance_lift_action_head messageEphemeral; exact whole _ (Framing.messageEphemeral_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head mixDh; exact whole _ (Framing.mixDh_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head mixPrecomputedDh; exact whole _ (Framing.mixPrecomputedDh_sameWGWorld _ _))
    | (maintenance_lift_action_head kdf; exact whole _ (Framing.kdf_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head kdfOut; exact whole _ (Framing.kdfOut_sameWGWorld _ _))
    | (maintenance_head peerDerefPrefix; exact AmbientContracts.drop (peerDerefPrefix_spec c (fun _ => True) _))
    | (maintenance_lift_action_head liftIndex; exact hi _)
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | with_reducible exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
    | with_reducible apply StatePrefixEnsures.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem setChainPrefix_preserves_product (c : ProductAmbientContracts I) (pid : PeerId) (ck hash : List UInt8) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (setChainPrefix pid ck hash)) :=
  ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) pid
    (fun p => {p with chainingKey := ck, hash}) (fun _ => rfl))

theorem addMacToPacketPrefix_preserves_product (c : ProductAmbientContracts I) (pid : PeerId) (msg : List UInt8) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (addMacToPacketPrefix pid msg)) := by
  apply ProductAmbientContracts.drop (Q := fun _ _ => True)
  simp only [addMacToPacketPrefix, liftWGObserver_bind, liftWGObserver_andPrefix, apply_ite, liftWGObserver_pure]
  apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  dsimp only
  apply PrefixEnsures.bind (c.setPeer (fun _ => True) pid
    {p with lastMac1Sent := blake2s 16 p.cookieMac1Key (msg.take (msg.length - 32)), haveSentMac1 := true})
  intro _
  apply PrefixEnsures.bind
  · unfold andPrefix
    apply PrefixEnsures.bind
      (c.nativeStore (fun _ => True) _ (by intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) _))
    intro valid
    split
    · exact c.nativeStore (fun _ => True) _ ((branchExpired_sameWGWorld _ _ _ _).of_factor wgStoreView wgStoreView (fun _ => rfl))
    · exact c.pure (fun _ => True) false
  · intro fresh
    split <;> exact c.pure (fun _ => True) _

theorem createInitiationPrefix_preserves_product (c : ProductAmbientContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (liftIndex (indexInsert owner)))))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (createInitiationPrefix pid)) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (StateT.lift a))) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  have whole {α : Type} (a : WG.M α) (ha : SameView (id : WGWorld → WGWorld) a) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) :=
    store a (ha.of_factor wgStoreView wgStoreView (fun _ => rfl))
  have branch_spec (d : Decision) (b : Bool) : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (Leanux.branch d b))) := by
    apply store
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) _
  have kdf_spec (second third : Bool) (ck data : List UInt8) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (kdf second third ck data))) :=
    whole _ (Framing.kdf_sameWGWorld second third ck data)
  have dev : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix getDev)) := by
    apply store
    intro initial
    unfold Hoare
    mvcgen [getDev, invariant, AmbientM.invariant]
  apply PrefixEnsures.preserves
  unfold createInitiationPrefix
  simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  repeat' first
    | simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
    | (maintenance_head setChainPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact setChainPrefix_preserves_product c _ _ _)
    | (maintenance_head modifyPeerKeysPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head getPeerMixed; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_lift_action_head getDev; change PrefixPreserves I LifetimeEvent.Safe _; exact dev)
    | (maintenance_lift_action_head hidden; change PrefixPreserves I LifetimeEvent.Safe _; exact ambient (AmbientM.hidden _))
    | (maintenance_lift_action_head generatePublic; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.generatePublic_sameWGWorld _))
    | (maintenance_lift_action_head messageEphemeral; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.messageEphemeral_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head mixDh; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.mixDh_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head mixPrecomputedDh; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.mixPrecomputedDh_sameWGWorld _ _))
    | (maintenance_lift_action_head kdf; change PrefixPreserves I LifetimeEvent.Safe _; exact kdf_spec _ _ _ _)
    | (maintenance_lift_action_head kdfOut; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.kdfOut_sameWGWorld _ _))
    | (maintenance_head peerDerefPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (c.peerDeref (fun _ => True) _))
    | (maintenance_lift_action_head liftIndex; change PrefixPreserves I LifetimeEvent.Safe _; exact hi _)
    | (maintenance_lift_action_head branch; change PrefixPreserves I LifetimeEvent.Safe _; exact branch_spec _ _)
    | (maintenance_lift_action_head invariant; change PrefixPreserves I LifetimeEvent.Safe _; exact ambient (AmbientM.invariant _))
    | exact PrefixEnsures.pure c.safe (fun _ _ hi => hi)
    | with_reducible apply PrefixEnsures.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals first
    | exact branch_spec _ _
    | exact kdf_spec _ _ _ _

theorem createResponsePrefix_preserves_product (c : ProductAmbientContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (liftIndex (indexInsert owner)))))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (createResponsePrefix pid)) := by
  have store {α : Type} (a : WG.M α) (ha : SameWGStore a) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) a ha)
  have ambient {α : Type} (a : AmbientM α) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (StateT.lift a))) :=
    store _ (by intro initial; exact hoare_liftAmbient a _)
  have whole {α : Type} (a : WG.M α) (ha : SameView (id : WGWorld → WGWorld) a) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix a)) :=
    store a (ha.of_factor wgStoreView wgStoreView (fun _ => rfl))
  have branch_spec (d : Decision) (b : Bool) : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (Leanux.branch d b))) := by
    apply store
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) _
  have kdf_spec (second third : Bool) (ck data : List UInt8) :
      PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (kdf second third ck data))) :=
    whole _ (Framing.kdf_sameWGWorld second third ck data)
  have dev : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix getDev)) := by
    apply store
    intro initial
    unfold Hoare
    mvcgen [getDev, invariant, AmbientM.invariant]
  apply PrefixEnsures.preserves
  unfold createResponsePrefix
  simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  repeat' first
    | simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
    | (maintenance_head setChainPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact setChainPrefix_preserves_product c _ _ _)
    | (maintenance_head modifyPeerKeysPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head getPeerMixed; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_lift_action_head getDev; change PrefixPreserves I LifetimeEvent.Safe _; exact dev)
    | (maintenance_lift_action_head hidden; change PrefixPreserves I LifetimeEvent.Safe _; exact ambient (AmbientM.hidden _))
    | (maintenance_lift_action_head generatePublic; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.generatePublic_sameWGWorld _))
    | (maintenance_lift_action_head messageEphemeral; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.messageEphemeral_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head mixDh; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.mixDh_sameWGWorld _ _ _ _))
    | (maintenance_lift_action_head mixPrecomputedDh; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.mixPrecomputedDh_sameWGWorld _ _))
    | (maintenance_lift_action_head kdf; change PrefixPreserves I LifetimeEvent.Safe _; exact kdf_spec _ _ _ _)
    | (maintenance_lift_action_head kdfOut; change PrefixPreserves I LifetimeEvent.Safe _; exact whole _ (Framing.kdfOut_sameWGWorld _ _))
    | (maintenance_head peerDerefPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (c.peerDeref (fun _ => True) _))
    | (maintenance_lift_action_head liftIndex; change PrefixPreserves I LifetimeEvent.Safe _; exact hi _)
    | (maintenance_lift_action_head branch; change PrefixPreserves I LifetimeEvent.Safe _; exact branch_spec _ _)
    | (maintenance_lift_action_head invariant; change PrefixPreserves I LifetimeEvent.Safe _; exact ambient (AmbientM.invariant _))
    | exact PrefixEnsures.pure c.safe (fun _ _ hi => hi)
    | with_reducible apply PrefixEnsures.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals first
    | exact branch_spec _ _
    | exact kdf_spec _ _ _ _

end Leanux.Proofs.WG.Lifetimes
