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
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

/-- The index table has no resolved object dereference. This frame transports
allocation safety while retaining the original device/record failures. -/
theorem indexInsert_identity_metadata (owner : IndexOwner) :
    SameView (fun w => (identityView w, allocationMetadata w)) (indexInsert owner) := by
  intro w x v hr
  have hf := indexInsert_sameIndexKernel owner w x v hr
  have he := congrArg (fun k => identityView {w with k}) hf
  have hm := congrArg (fun k => allocationMetadata {w with k}) hf
  apply Prod.ext
  · change identityView v = identityView w
    unfold identityView Peers.snapshot keypairResidents packetResidents at he ⊢
    simpa [indexKernelView, indexKernel, Option.bind_map, Function.comp_def] using he
  · change allocationMetadata v = allocationMetadata w
    unfold allocationMetadata deviceAllocationMetadata at hm ⊢
    simpa [indexKernelView, indexKernel, Option.map_map, Function.comp_def] using hm

theorem indexInsert_allocation (owner : IndexOwner) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (liftPrefix (indexInsert owner)) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  have hf := indexInsert_identity_metadata owner w x v hr
  exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

def setChainPrefix (pid : PeerId) (ck hash : List UInt8) : MixedM Unit :=
  modifyPeerKeysPrefix pid fun p => {p with chainingKey := ck, hash}

theorem setChainPrefix_erases (pid : PeerId) (ck hash : List UInt8) :
    ErasesPrefix (setChainPrefix pid ck hash)
      ((pinned_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck hash) :=
  modifyPeerKeysPrefix_erases pid _

theorem setChainPrefix_preserves (c : AmbientContracts I) (pid : PeerId) (ck hash : List UInt8) :
    PrefixPreserves I LifetimeEvent.Safe (setChainPrefix pid ck hash) :=
  AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
    (fun p => {p with chainingKey := ck, hash}) (fun _ => rfl))

def createInitiationPrefix (pid : PeerId) : MixedM (Option (List UInt8)) := do
  let identity := (← liftPrefix getDev).staticIdentity
  if ← liftPrefix (branch .initNoIdentity !identity.hasIdentity) then return none
  let p ← getPeerMixed pid
  let h := noiseHash (handshakeInitHash ++ p.remoteStatic)
  setChainPrefix pid handshakeInitChainingKey h
  let secret := clamp (← liftPrefix (hidden .initEphemeral))
  modifyPeerKeysPrefix pid fun p => {p with ephemeralPrivate := secret}
  let (pub, ok) ← liftPrefix (generatePublic secret)
  if ← liftPrefix (branch .initNoEphemeral !ok) then return none
  let some e := pub | liftPrefix (invariant "unreachable")
  let (ck, h) ← liftPrefix (messageEphemeral false e handshakeInitChainingKey h)
  setChainPrefix pid ck h
  let es ← liftPrefix (mixDh true ck secret p.remoteStatic)
  if ← liftPrefix (branch .initEsFailed es.isNone) then return none
  let some (ck, key) := es | liftPrefix (invariant "unreachable")
  let encStatic := aeadEncrypt key noiseNonce identity.staticPublic h
  let h := noiseHash (h ++ encStatic)
  setChainPrefix pid ck h
  let ss ← liftPrefix (mixPrecomputedDh ck p.precomputedStaticStatic)
  if ← liftPrefix (branch .initSsFailed ss.isNone) then return none
  let some (ck, key) := ss | liftPrefix (invariant "unreachable")
  let timestamp := tai64n (← liftPrefix (hidden .tai64nNow))
  let encTime := aeadEncrypt key noiseNonce timestamp h
  let h := noiseHash (h ++ encTime)
  setChainPrefix pid ck h
  _ ← peerDerefPrefix (.handshake pid)
  let index ← liftPrefix (indexInsert (.handshake pid))
  modifyPeerKeysPrefix pid fun p => {p with handshakeState := HANDSHAKE_CREATED_INITIATION}
  return some (le32 1 ++ le32 index ++ e ++ encStatic ++ encTime ++ List.replicate 32 0)

def createResponsePrefix (pid : PeerId) : MixedM (Option (List UInt8)) := do
  let p ← getPeerMixed pid
  if ← liftPrefix (branch .respNotConsumed (p.handshakeState != HANDSHAKE_CONSUMED_INITIATION)) then return none
  let receiver := p.remoteIndex
  let secret := clamp (← liftPrefix (hidden .respEphemeral))
  modifyPeerKeysPrefix pid fun p => {p with ephemeralPrivate := secret}
  let (pub, ok) ← liftPrefix (generatePublic secret)
  if ← liftPrefix (branch .respNoEphemeral !ok) then return none
  let some e := pub | liftPrefix (invariant "unreachable")
  let (ck, h) ← liftPrefix (messageEphemeral false e p.chainingKey p.hash)
  setChainPrefix pid ck h
  let ee ← liftPrefix (mixDh false ck secret p.remoteEphemeral)
  if ← liftPrefix (branch .respEeFailed ee.isNone) then return none
  let some (ck, _) := ee | liftPrefix (invariant "unreachable")
  setChainPrefix pid ck h
  let se ← liftPrefix (mixDh false ck secret p.remoteStatic)
  if ← liftPrefix (branch .respSeFailed se.isNone) then return none
  let some (ck, _) := se | liftPrefix (invariant "unreachable")
  let outs ← liftPrefix (kdf true true ck p.presharedKey)
  let (ck, tempHash, key) := (← liftPrefix (kdfOut outs 0), ← liftPrefix (kdfOut outs 1), ← liftPrefix (kdfOut outs 2))
  let h := noiseHash (h ++ tempHash)
  let encNothing := aeadEncrypt key noiseNonce [] h
  let h := noiseHash (h ++ encNothing)
  setChainPrefix pid ck h
  _ ← peerDerefPrefix (.handshake pid)
  let index ← liftPrefix (indexInsert (.handshake pid))
  modifyPeerKeysPrefix pid fun p => {p with handshakeState := HANDSHAKE_CREATED_RESPONSE}
  return some (le32 2 ++ le32 index ++ le32 receiver ++ e ++ encNothing ++ List.replicate 32 0)

def addMacToPacketPrefix (pid : PeerId) (msg : List UInt8) : MixedM (List UInt8) := do
  let p ← getPeerMixed pid
  let body := msg.take (msg.length - 32)
  let mac1 := blake2s 16 p.cookieMac1Key body
  setPeerMixed pid {p with lastMac1Sent := mac1, haveSentMac1 := true}
  if ← andPrefix (liftPrefix (branch .addMacCookieValid p.cookieIsValid))
      (liftPrefix (branchExpired .addMacCookieFresh p.cookieBirthdate COOKIE_FRESH_SECONDS (!·))) then
    return body ++ mac1 ++ blake2s 16 p.cookie (body ++ mac1)
  return body ++ mac1 ++ List.replicate 16 0

theorem createInitiationPrefix_erases (pid : PeerId) :
    ErasesPrefix (createInitiationPrefix pid) (createInitiation pid) := by
  unfold createInitiationPrefix createInitiation modifyPeerKeysPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact setChainPrefix_erases _ _ _
    | with_reducible exact modifyPeerKeysPrefix_erases _ _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact peerDerefPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _

theorem createResponsePrefix_erases (pid : PeerId) :
    ErasesPrefix (createResponsePrefix pid) (createResponse pid) := by
  unfold createResponsePrefix createResponse modifyPeerKeysPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact setChainPrefix_erases _ _ _
    | with_reducible exact modifyPeerKeysPrefix_erases _ _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact peerDerefPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _

theorem addMacToPacketPrefix_erases (pid : PeerId) (msg : List UInt8) :
    ErasesPrefix (addMacToPacketPrefix pid msg) (addMacToPacket pid msg) := by
  unfold addMacToPacketPrefix addMacToPacket
  repeat' first
    | with_reducible exact setChainPrefix_erases _ _ _
    | with_reducible exact modifyPeerKeysPrefix_erases _ _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact peerDerefPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals first | exact erasesPrefix_lift _ | exact erasesPrefix_pure _

theorem addMacToPacketPrefix_preserves (c : AmbientContracts I) (pid : PeerId) (msg : List UInt8) :
    PrefixPreserves I LifetimeEvent.Safe (addMacToPacketPrefix pid msg) := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  unfold addMacToPacketPrefix
  apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  dsimp only
  apply PrefixEnsures.bind (c.setPeer (fun _ => True) pid
    {p with lastMac1Sent := blake2s 16 p.cookieMac1Key (msg.take (msg.length - 32)), haveSentMac1 := true})
  intro _
  apply PrefixEnsures.bind
  · unfold andPrefix
    apply PrefixEnsures.bind (c.branch (fun _ => True) _ _)
    intro valid
    split
    · exact c.kernel (fun _ => True) _ (branchExpired_sameKernel _ _ _ _)
    · exact c.pure (fun _ => True) false
  · intro fresh
    split <;> exact c.pure (fun _ => True) _

theorem createInitiationPrefix_preserves (c : AmbientContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (indexInsert owner)))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (createInitiationPrefix pid) := by
  unfold createInitiationPrefix
  repeat' first
    | with_reducible exact setChainPrefix_preserves c _ _ _
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (hidden_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.generatePublic_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.messageEphemeral_sameKernel _ _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.mixDh_sameKernel _ _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.mixPrecomputedDh_sameKernel _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.kdf_sameKernel _ _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.kdfOut_sameKernel _ _))
    | with_reducible exact AmbientContracts.drop (peerDerefPrefix_spec c (fun _ => True) _)
    | with_reducible exact hi _
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem createResponsePrefix_preserves (c : AmbientContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (indexInsert owner)))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (createResponsePrefix pid) := by
  unfold createResponsePrefix
  repeat' first
    | with_reducible exact setChainPrefix_preserves c _ _ _
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (hidden_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.generatePublic_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.messageEphemeral_sameKernel _ _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.mixDh_sameKernel _ _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.mixPrecomputedDh_sameKernel _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.kdf_sameKernel _ _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Framing.kdfOut_sameKernel _ _))
    | with_reducible exact AmbientContracts.drop (peerDerefPrefix_spec c (fun _ => True) _)
    | with_reducible exact hi _
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

end Leanux.Proofs.WG.Lifetimes
