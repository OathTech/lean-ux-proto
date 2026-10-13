import Leanux.Proofs.WG.Lifetimes.HandshakeConstruct

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Complete original Noise consumption. Reference-taking lookups and every
failure put are observed, as are all fresh peer accesses after authentication.
These contracts concern resolved identities, not cryptographic validity or
ownership of the table's scalar references. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def consumeInitiationPrefix (msg : List UInt8) : MixedM (Option PeerId) := do
  let out (peer : Option PeerId) (ret : Option PeerId) : MixedM (Option PeerId) := do
    if ← liftPrefix (branch .consumeFailedPut ret.isNone) then peerPutMixed peer
    return ret
  let identity := (← liftPrefix getDev).staticIdentity
  if ← liftPrefix (branch .consumeNoIdentity !identity.hasIdentity) then return ← out none none
  let hash := noiseHash (handshakeInitHash ++ identity.staticPublic)
  let e := (msg.drop 8).take 32
  let (ck, hash) ← liftPrefix (messageEphemeral true e handshakeInitChainingKey hash)
  let es ← liftPrefix (mixDh true ck identity.staticPrivate e)
  if ← liftPrefix (branch .consumeEsFailed es.isNone) then return ← out none none
  let some (ck, key) := es | liftPrefix (invariant "unreachable")
  let st ← liftPrefix (messageDecrypt ((msg.drop 40).take 48) key hash)
  if ← liftPrefix (branch .consumeStaticFailed st.isNone) then return ← out none none
  let some (s, hash) := st | liftPrefix (invariant "unreachable")
  let peer ← pubkeyLookupPrefix s
  if ← liftPrefix (branch .consumeNoPeer peer.isNone) then return ← out none none
  let some pid := peer | liftPrefix (invariant "unreachable")
  let ss ← liftPrefix (mixPrecomputedDh ck (← getPeerMixed pid).precomputedStaticStatic)
  if ← liftPrefix (branch .consumeSsFailed ss.isNone) then return ← out peer none
  let some (ckSs, key) := ss | liftPrefix (invariant "unreachable")
  let ts ← liftPrefix (messageDecrypt ((msg.drop 88).take 28) key hash)
  if ← liftPrefix (branch .consumeTimestampFailed ts.isNone) then return ← out peer none
  let some (t, hashT) := ts | liftPrefix (invariant "unreachable")
  let p ← getPeerMixed pid
  let replay := memcmp t p.latestTimestamp != .gt
  let floodLhs : Int64 := p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64
  let now ← liftPrefix (hiddenClock64 .floodNow)
  if ← liftPrefix (WG.orM (branch .consumeReplay replay)
      (branchCmp .consumeFlood (floodLhs > now) floodLhs.toInt now.toInt)) then
    return ← out peer none
  modifyPeerKeysPrefix pid fun p => {p with remoteEphemeral := e}
  if ← liftPrefix (branch .consumeNewerTimestamp (memcmp t p.latestTimestamp == .gt)) then
    modifyPeerKeysPrefix pid fun p => {p with latestTimestamp := t}
  modifyPeerKeysPrefix pid fun p => {p with hash := hashT, chainingKey := ckSs, remoteIndex := u32le msg 4}
  let consumption ← liftPrefix (hiddenClock64 .consumptionNow)
  let last := (← getPeerMixed pid).lastInitiationConsumption
  let diff : Int64 := last - consumption
  if ← liftPrefix (branchCmp .consumeLaterTime (diff < 0) diff.toInt 0) then
    modifyPeerKeysPrefix pid fun p => {p with lastInitiationConsumption := consumption}
  modifyPeerKeysPrefix pid fun p => {p with handshakeState := HANDSHAKE_CONSUMED_INITIATION}
  out peer (some pid)

def consumeResponsePrefix (msg : List UInt8) : MixedM (Option PeerId) := do
  let identity := (← liftPrefix getDev).staticIdentity
  if ← liftPrefix (branch .crespNoIdentity !identity.hasIdentity) then return none
  let entry ← indexLookupPrefix [.handshake] (u32le msg 8)
  if ← liftPrefix (branch .crespNoHandshake entry.isNone) then return none
  let some e := entry | liftPrefix (invariant "unreachable")
  let pid := e.peer
  let fail : MixedM (Option PeerId) := do
    peerPutMixed (some pid)
    return none
  let p ← getPeerMixed pid
  let state := p.handshakeState
  if ← liftPrefix (branch .crespNotCreatedInitiation (state != HANDSHAKE_CREATED_INITIATION)) then return ← fail
  let eph := (msg.drop 12).take 32
  let (ck, h) ← liftPrefix (messageEphemeral true eph p.chainingKey p.hash)
  let ee ← liftPrefix (mixDh false ck p.ephemeralPrivate eph)
  if ← liftPrefix (branch .crespEeFailed ee.isNone) then return ← fail
  let some (ck, _) := ee | liftPrefix (invariant "unreachable")
  let se ← liftPrefix (mixDh false ck identity.staticPrivate eph)
  if ← liftPrefix (branch .crespSeFailed se.isNone) then return ← fail
  let some (ck, _) := se | liftPrefix (invariant "unreachable")
  let outs ← liftPrefix (kdf true true ck p.presharedKey)
  let (ck, tempHash, key) := (← liftPrefix (kdfOut outs 0), ← liftPrefix (kdfOut outs 1), ← liftPrefix (kdfOut outs 2))
  let h := noiseHash (h ++ tempHash)
  let dec ← liftPrefix (messageDecrypt ((msg.drop 44).take 16) key h)
  if ← liftPrefix (branch .crespDecryptFailed dec.isNone) then return ← fail
  let some (_, h) := dec | liftPrefix (invariant "unreachable")
  if ← liftPrefix (branch .crespStateChanged ((← getPeerMixed pid).handshakeState != state)) then return ← fail
  modifyPeerKeysPrefix pid fun p => {p with remoteEphemeral := eph, hash := h, chainingKey := ck, remoteIndex := u32le msg 4, handshakeState := HANDSHAKE_CONSUMED_RESPONSE}
  return some pid

theorem consumeReject_sameKernel (replay : Bool) (lhs now : Int64) :
    SameKernel (WG.orM (branch .consumeReplay replay)
      (branchCmp .consumeFlood (lhs > now) lhs.toInt now.toInt)) := by
  unfold WG.orM
  apply sameKernel_bind (sameKernel_branch _ _)
  intro yes
  split
  · exact sameKernel_pure _
  · exact branchCmp_sameKernel _ _ _ _

theorem consumeInitiationPrefix_erases (msg : List UInt8) :
    ErasesPrefix (consumeInitiationPrefix msg) (consumeInitiation msg) := by
  unfold consumeInitiationPrefix consumeInitiation modifyPeerKeysPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact modifyPeerKeysPrefix_erases _ _
    | with_reducible exact pubkeyLookupPrefix_erases _
    | with_reducible exact indexLookupPrefix_erases _ _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals first
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | exact getPeerMixed_erases _
    | exact setPeerMixed_erases _ _
    | exact peerPutMixed_erases _

theorem consumeInitiationPrefix_preserves (c : AmbientContracts I) (msg : List UInt8) :
    PrefixPreserves I LifetimeEvent.Safe (consumeInitiationPrefix msg) := by
  unfold consumeInitiationPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact pubkeyLookupPrefix_preserves_ambient c _
    | with_reducible exact indexLookupPrefix_preserves_ambient c _ _
    | with_reducible exact c.peerPut _
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (hiddenClock64_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (consumeReject_sameKernel _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.messageEphemeral_sameKernel _ _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.mixDh_sameKernel _ _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.mixPrecomputedDh_sameKernel _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.messageDecrypt_sameKernel _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.kdf_sameKernel _ _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.kdfOut_sameKernel _ _))
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.branchCmp (fun _ => True) _ _ _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem consumeResponsePrefix_erases (msg : List UInt8) :
    ErasesPrefix (consumeResponsePrefix msg) (consumeResponse msg) := by
  unfold consumeResponsePrefix consumeResponse modifyPeerKeysPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact modifyPeerKeysPrefix_erases _ _
    | with_reducible exact pubkeyLookupPrefix_erases _
    | with_reducible exact indexLookupPrefix_erases _ _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals first
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | exact getPeerMixed_erases _
    | exact setPeerMixed_erases _ _
    | exact peerPutMixed_erases _

theorem consumeResponsePrefix_preserves (c : AmbientContracts I) (msg : List UInt8) :
    PrefixPreserves I LifetimeEvent.Safe (consumeResponsePrefix msg) := by
  unfold consumeResponsePrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact pubkeyLookupPrefix_preserves_ambient c _
    | with_reducible exact indexLookupPrefix_preserves_ambient c _ _
    | with_reducible exact c.peerPut _
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (hiddenClock64_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (consumeReject_sameKernel _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.messageEphemeral_sameKernel _ _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.mixDh_sameKernel _ _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.mixPrecomputedDh_sameKernel _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.messageDecrypt_sameKernel _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.kdf_sameKernel _ _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.kdfOut_sameKernel _ _))
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.branchCmp (fun _ => True) _ _ _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

end Leanux.Proofs.WG.Lifetimes
