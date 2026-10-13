import Leanux.Proofs.WG.Lifetimes.SocketCalls
import Leanux.Proofs.WG.Lifetimes.ReceiveCompletion

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Complete TX completion helpers. Socket transmission uses the concrete
IPv4/IPv6 observers, including loopback's saved-peer scan. Ordinary send errors
remain Boolean results; Stops retain all preceding resolved accesses. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def sendSkbToPeerPrefix (pid : PeerId) (bytes : List UInt8) (ds : Nat) : MixedM Bool := do
  let p ← getPeerMixed pid
  let family := (p.endpoint.map (·.family)).getD 0
  let e := p.endpoint.getD {family := 0, addr := 0, port := 0}
  let ret ← do
    if ← liftPrefix (branch .sendSkbInet (family == AF_INET)) then send4Prefix e (some pid) bytes ds true
    else if ← liftPrefix (branch .sendSkbInet6 (family == AF_INET6)) then send6Prefix e (some pid) bytes ds true
    else pure (-EAFNOSUPPORT)
  let sent := ret == 0
  if ← liftPrefix (branch .sendSkbOk sent) then
    modifyPeerKeysPrefix pid fun p => {p with txBytes := p.txBytes + bytes.length}
  return sent

def timersDataSentPrefix (pid : PeerId) : MixedM Unit := do
  if ← liftPrefix (branch .timersDataSentNotPending !((← getPeerMixed pid).timerPending .newHandshake)) then
    let jitter ← liftPrefix (jitterBelowRekeyTimeout .newHandshakeJitter)
    if ← modPeerTimerGuardPrefix pid then
      armTimerPrefix pid .newHandshake (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter)

def timersAnyAuthenticatedPacketSentPrefix (pid : PeerId) : MixedM Unit :=
  delTimerPrefix pid .sendKeepalive

def keepKeyFreshPrefix (pid : PeerId) : MixedM Unit := do
  let current := (← getPeerMixed pid).keypairCurrent
  let send ← andPrefix (liftPrefix (branch .freshKeypair current.isSome)) do
    let some id := current | liftPrefix (invariant "unreachable")
    let k ← getKeypairPrefix id
    andPrefix (liftPrefix (branch .freshValid k.sending.isValid)) do
      orPrefix (liftPrefix (branchCmp .freshCounter (k.sendingCounter > REKEY_AFTER_MESSAGES)
        k.sendingCounter REKEY_AFTER_MESSAGES)) do
        andPrefix (liftPrefix (branch .freshInitiator k.iAmTheInitiator)) do
          liftPrefix (branchExpired .freshExpired k.sending.birthdate REKEY_AFTER_TIME)
  if ← liftPrefix (branch .freshSend send) then sendQueuedHandshakeInitiationPrefix pid false

def createDataDonePrefix (pid : PeerId) (item : List SkbId) : MixedM Unit := do
  timersTraversalPrefix pid
  timersAnyAuthenticatedPacketSentPrefix pid
  let mut dataSent := false
  for id in item do
    let skb ← getTxSkbPrefix id
    _ ← liftPrefix (branch .doneSkbIterate true)
    let isKeepalive := skb.bytes.length == MESSAGE_DATA_LEN_0
    let sent ← sendSkbToPeerPrefix pid skb.bytes skb.ds
    if ← andPrefix (liftPrefix (branch .doneSendOk sent))
        (liftPrefix (branch .doneNotKeepalive !isKeepalive)) then dataSent := true
  _ ← liftPrefix (branch .doneSkbIterate false)
  if ← liftPrefix (branch .doneDataSent dataSent) then timersDataSentPrefix pid
  keepKeyFreshPrefix pid

theorem sendSkbToPeerPrefix_erases (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    ErasesPrefix (sendSkbToPeerPrefix pid bytes ds) (sendSkbToPeer pid bytes ds) := by
  unfold sendSkbToPeerPrefix sendSkbToPeer modifyPeerKeysPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact send4Prefix_erases _ _ _ _ _
    | with_reducible exact send6Prefix_erases _ _ _ _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem timersDataSentPrefix_erases (pid : PeerId) :
    ErasesPrefix (timersDataSentPrefix pid) (timersDataSent pid) := by
  unfold timersDataSentPrefix timersDataSent
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact modPeerTimerGuardPrefix_erases _
    | with_reducible exact armTimerPrefix_erases _ _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem timersAnyAuthenticatedPacketSentPrefix_erases (pid : PeerId) :
    ErasesPrefix (timersAnyAuthenticatedPacketSentPrefix pid) (timersAnyAuthenticatedPacketSent pid) :=
  delTimerPrefix_erases pid .sendKeepalive

theorem keepKeyFreshPrefix_erases (pid : PeerId) :
    ErasesPrefix (keepKeyFreshPrefix pid) (keepKeyFresh pid) := by
  unfold keepKeyFreshPrefix keepKeyFresh
  apply erasesPrefix_bind (getPeerMixed_erases pid)
  intro p
  apply erasesPrefix_bind
  · apply andPrefix_erases (erasesPrefix_lift _)
    cases he : p.keypairCurrent with
    | none => exact erasesPrefix_lift _
    | some id =>
      apply erasesPrefix_bind (getKeypairPrefix_erases id)
      intro k
      exact andPrefix_erases (erasesPrefix_lift _)
        (orPrefix_erases (erasesPrefix_lift _)
          (andPrefix_erases (erasesPrefix_lift _) (erasesPrefix_lift _)))
  · intro send
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro yes
    split
    · exact sendQueuedHandshakeInitiationPrefix_erases pid false
    · exact erasesPrefix_pure _

theorem createDataDonePrefix_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (createDataDonePrefix pid item) (createDataDone pid item) := by
  unfold createDataDonePrefix createDataDone
  repeat' first
    | with_reducible exact timersTraversalPrefix_erases _
    | with_reducible exact timersAnyAuthenticatedPacketSentPrefix_erases _
    | with_reducible exact timersDataSentPrefix_erases _
    | with_reducible exact keepKeyFreshPrefix_erases _
    | with_reducible exact sendSkbToPeerPrefix_erases _ _ _
    | with_reducible exact getTxSkbPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply andPrefix_erases
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem sendSkbToPeerPrefix_spec (c : AmbientContracts I) (sc : SocketContracts I)
    (P : IdentityView → Prop) (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    AmbientSpec I P (sendSkbToPeerPrefix pid bytes ds) (fun _ => P) := by
  unfold sendSkbToPeerPrefix
  repeat' first
    | with_reducible exact c.getPeer_frame P _
    | with_reducible exact c.branch P _ _
    | with_reducible exact send4Prefix_spec c sc P _ _ _ _ _
    | with_reducible exact send6Prefix_spec c sc P _ _ _ _ _
    | with_reducible exact (modifyPeerKeysPrefix_spec_ambient c P pid
        (fun p => {p with txBytes := p.txBytes + bytes.length}) (fun _ => rfl))
    | with_reducible exact c.pure P _
    | with_reducible apply PrefixEnsures.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem timersDataSentPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (timersDataSentPrefix pid) (fun _ => P) := by
  unfold timersDataSentPrefix
  repeat' first
    | with_reducible exact c.getPeer_frame P _
    | with_reducible exact c.branch P _ _
    | with_reducible exact c.kernel P _ (jitterBelowRekeyTimeout_sameKernel _)
    | with_reducible exact modPeerTimerGuardPrefix_spec c P _
    | with_reducible exact armTimerPrefix_spec c P _ _ _
    | with_reducible exact c.pure P _
    | with_reducible apply PrefixEnsures.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem timersAnyAuthenticatedPacketSentPrefix_spec (c : AmbientContracts I)
    (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (timersAnyAuthenticatedPacketSentPrefix pid) (fun _ => P) :=
  delTimerPrefix_spec c P pid .sendKeepalive

theorem keepKeyFreshPrefix_preserves (c : AmbientContracts I)
    (hq : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (keepKeyFreshPrefix pid) := by
  unfold keepKeyFreshPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.getKeypair_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.branchCmp (fun _ => True) _ _ _ _)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (branchExpired_sameKernel _ _ _))
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact sendQueuedHandshakeInitiationPrefix_preserves_ambient c hq _ _
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply andPrefix_preserves c.safe
    | with_reducible apply orPrefix_preserves c.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem createDataDonePrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (sc : SocketContracts I) (pid : PeerId) (item : List SkbId) :
    PrefixPreserves I LifetimeEvent.Safe (createDataDonePrefix pid item) := by
  have fresh := keepKeyFreshPrefix_preserves c
    (fun pid => AmbientContracts.drop (t.device (fun _ => True) (.handshake pid))) pid
  unfold createDataDonePrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (timersTraversalPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (timersAnyAuthenticatedPacketSentPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (timersDataSentPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (sendSkbToPeerPrefix_spec c sc (fun _ => True) _ _ _)
    | with_reducible exact fresh
    | with_reducible exact AmbientContracts.drop (t.get (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply andPrefix_preserves c.safe
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

/-- A jitter failure occurs after the pending-timer read and before the timer
guard. Premises describe consecutive original runs, not a desired log. -/
theorem timersDataSentPrefix_jitter_failure (pid : PeerId) (w entered : World)
    (p : Peer) (h : List LifetimeEvent) (e : Stop)
    (hp : (getPeer pid).run w = .ok (p, w))
    (hb : (branch .timersDataSentNotPending !(p.timerPending .newHandshake)).run w = .ok (true, entered))
    (hj : (jitterBelowRekeyTimeout .newHandshakeJitter).run entered = .error e) :
    runPrefix (timersDataSentPrefix pid) w h = (.error e, h ++ [.peer (.read pid p.internalId)]) := by
  simp only [timersDataSentPrefix, runPrefix_bind, getPeerMixed_run, hp,
    runPrefix_lift, hb, ↓reduceIte, hj]

end Leanux.Proofs.WG.Lifetimes
