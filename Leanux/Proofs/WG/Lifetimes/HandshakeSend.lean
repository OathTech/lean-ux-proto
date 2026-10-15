import Leanux.Proofs.WG.Lifetimes.HandshakeCalls
import Leanux.Proofs.WG.Lifetimes.TxCompletion
import Leanux.Proofs.WG.Lifetimes.Session

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Complete original handshake send calls. Allocation refusal and ordinary
negative socket returns are normal returns; Stops retain their access prefix
and skip later timer work or the worker's final put. No scheduler or saved
reference ownership assertion is added. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

/-- The original buffer helper is an allocation check followed by the original
socket send, with its Boolean return discarded. This equality has no premise. -/
theorem sendBufferToPeer_eq (pid : PeerId) (bytes : List UInt8) :
    sendBufferToPeer pid bytes = (do
      if ← branch .sendBufNoMem !(← hiddenAlloc .sendBufSkb) then return
      discard <| sendSkbToPeer pid bytes HANDSHAKE_DSCP) := by
  have bind_if {α β : Type} (p : Prop) [Decidable p] (a b : M α) (f : α → M β) :
      ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
    split <;> rfl
  simp only [sendBufferToPeer, sendSkbToPeer, Functor.discard, map_const,
    Function.comp_apply, Function.const, map_eq_pure_bind, bind_assoc, pure_bind,
    bind_if, bind_pure_unit]

def sendBufferToPeerPrefix (pid : PeerId) (bytes : List UInt8) : MixedM Unit := do
  if ← liftPrefix (branch .sendBufNoMem !(← liftPrefix (hiddenAlloc .sendBufSkb))) then return
  discard <| sendSkbToPeerPrefix pid bytes HANDSHAKE_DSCP

def timersSessionDerivedPrefix (pid : PeerId) : MixedM Unit :=
  discard <| modPeerTimerPrefix .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS

def timersHandshakeInitiatedPrefix (pid : PeerId) : MixedM Unit := do
  let jc ← liftPrefix (callerJiffies .timerJiffiesHandshakeInitiated)
  let jitter ← liftPrefix (jitterBelowRekeyTimeout .retransmitJitter)
  if ← modPeerTimerGuardPrefix pid then
    armTimerPrefix pid .retransmitHandshake (REKEY_TIMEOUT_TICKS + jitter) jc

def sendHandshakeInitiationPrefix (pid : PeerId) : MixedM Unit := do
  if ← liftPrefix (branchExpired .initRateLimited (← getPeerMixed pid).lastSentHandshake REKEY_TIMEOUT (!·)) then return
  let now ← liftPrefix (hiddenClock64 .initLastSent)
  modifyPeerKeysPrefix pid fun p => {p with lastSentHandshake := now}
  let created ← createInitiationPrefix pid
  if ← liftPrefix (branch .initCreated created.isSome) then
    let some msg := created | liftPrefix (invariant "unreachable")
    let msg ← addMacToPacketPrefix pid msg
    timersTraversalPrefix pid
    timersAnyAuthenticatedPacketSentPrefix pid
    let now ← liftPrefix (hiddenClock64 .initLastSentAgain)
    modifyPeerKeysPrefix pid fun p => {p with lastSentHandshake := now}
    sendBufferToPeerPrefix pid msg
    timersHandshakeInitiatedPrefix pid

def sendHandshakeResponsePrefix (pid : PeerId) : MixedM Unit := do
  let now ← liftPrefix (hiddenClock64 .respLastSent)
  modifyPeerKeysPrefix pid fun p => {p with lastSentHandshake := now}
  let created ← createResponsePrefix pid
  if ← liftPrefix (branch .respCreated created.isSome) then
    let some msg := created | liftPrefix (invariant "unreachable")
    let msg ← addMacToPacketPrefix pid msg
    if ← liftPrefix (branch .respSessionBegun (← beginSessionPrefix pid)) then
      timersSessionDerivedPrefix pid
      timersTraversalPrefix pid
      timersAnyAuthenticatedPacketSentPrefix pid
      let now ← liftPrefix (hiddenClock64 .respLastSentAgain)
      modifyPeerKeysPrefix pid fun p => {p with lastSentHandshake := now}
      sendBufferToPeerPrefix pid msg

def handshakeSendWorkerPrefix (pid : PeerId) : MixedM Unit := do
  sendHandshakeInitiationPrefix pid
  peerPutMixed (some pid)

theorem sendBufferToPeerPrefix_erases (pid : PeerId) (bytes : List UInt8) :
    ErasesPrefix (sendBufferToPeerPrefix pid bytes) (sendBufferToPeer pid bytes) := by
  rw [sendBufferToPeer_eq]
  unfold sendBufferToPeerPrefix
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | with_reducible exact sendSkbToPeerPrefix_erases _ _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem timersSessionDerivedPrefix_erases (pid : PeerId) :
    ErasesPrefix (timersSessionDerivedPrefix pid) (timersSessionDerived pid) := by
  exact erasesPrefix_bind (modPeerTimerPrefix_erases _ pid _ _) (fun _ => erasesPrefix_pure _)

theorem timersHandshakeInitiatedPrefix_erases (pid : PeerId) :
    ErasesPrefix (timersHandshakeInitiatedPrefix pid) (timersHandshakeInitiated pid) := by
  unfold timersHandshakeInitiatedPrefix timersHandshakeInitiated
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro jc
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro jitter
  apply erasesPrefix_bind (modPeerTimerGuardPrefix_erases pid)
  intro yes
  apply erasesPrefix_ite
  · intro _; exact armTimerPrefix_erases _ _ _ _
  · intro _; exact erasesPrefix_pure _

theorem sendHandshakeInitiationPrefix_erases (pid : PeerId) :
    ErasesPrefix (sendHandshakeInitiationPrefix pid) (sendHandshakeInitiation pid) := by
  unfold sendHandshakeInitiationPrefix sendHandshakeInitiation modifyPeerKeysPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact createInitiationPrefix_erases _
    | with_reducible exact addMacToPacketPrefix_erases _ _
    | with_reducible exact timersTraversalPrefix_erases _
    | with_reducible exact timersAnyAuthenticatedPacketSentPrefix_erases _
    | with_reducible exact sendBufferToPeerPrefix_erases _ _
    | with_reducible exact timersHandshakeInitiatedPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all

theorem sendHandshakeResponsePrefix_erases (pid : PeerId) :
    ErasesPrefix (sendHandshakeResponsePrefix pid) (sendHandshakeResponse pid) := by
  unfold sendHandshakeResponsePrefix sendHandshakeResponse modifyPeerKeysPrefix
  simp only [bind_assoc]
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact createResponsePrefix_erases _
    | with_reducible exact addMacToPacketPrefix_erases _ _
    | with_reducible exact beginSessionPrefix_erases _
    | with_reducible exact timersSessionDerivedPrefix_erases _
    | with_reducible exact timersTraversalPrefix_erases _
    | with_reducible exact timersAnyAuthenticatedPacketSentPrefix_erases _
    | with_reducible exact sendBufferToPeerPrefix_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all

theorem handshakeSendWorkerPrefix_erases (pid : PeerId) :
    ErasesPrefix (handshakeSendWorkerPrefix pid) (handshakeSendWorker pid) :=
  erasesPrefix_bind (sendHandshakeInitiationPrefix_erases pid) (fun _ => peerPutMixed_erases _)

theorem sendBufferToPeerPrefix_spec (c : AmbientContracts I) (sc : SocketContracts I)
    (P : IdentityView → Prop) (pid : PeerId) (bytes : List UInt8) :
    AmbientSpec I P (sendBufferToPeerPrefix pid bytes) (fun _ => P) := by
  unfold sendBufferToPeerPrefix
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | with_reducible exact c.kernel P _ (hiddenAlloc_sameKernel _)
    | with_reducible exact c.branch P _ _
    | with_reducible exact sendSkbToPeerPrefix_spec c sc P _ _ _
    | with_reducible exact c.pure P _
    | with_reducible apply PrefixEnsures.bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem timersSessionDerivedPrefix_spec (c : AmbientContracts I)
    (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (timersSessionDerivedPrefix pid) (fun _ => P) :=
  PrefixEnsures.bind (modPeerTimerPrefix_spec c P _ pid _ _) (fun _ => c.pure P _)

theorem timersHandshakeInitiatedPrefix_spec (c : AmbientContracts I)
    (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (timersHandshakeInitiatedPrefix pid) (fun _ => P) := by
  unfold timersHandshakeInitiatedPrefix
  apply PrefixEnsures.bind (c.kernel P _ (callerJiffies_sameKernel _))
  intro jc
  apply PrefixEnsures.bind (c.kernel P _ (jitterBelowRekeyTimeout_sameKernel _))
  intro jitter
  apply PrefixEnsures.bind (modPeerTimerGuardPrefix_spec c P pid)
  intro yes
  split
  · exact armTimerPrefix_spec c P _ _ _ _
  · exact c.pure P _

theorem sendHandshakeInitiationPrefix_preserves (c : AmbientContracts I) (sc : SocketContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (indexInsert owner)))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (sendHandshakeInitiationPrefix pid) := by
  unfold sendHandshakeInitiationPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (branchExpired_sameKernel _ _ _ _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (hiddenClock64_sameKernel _))
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact createInitiationPrefix_preserves c hi _
    | with_reducible exact addMacToPacketPrefix_preserves c _ _
    | with_reducible exact AmbientContracts.drop (timersTraversalPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (timersAnyAuthenticatedPacketSentPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (sendBufferToPeerPrefix_spec c sc (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (timersHandshakeInitiatedPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem sendHandshakeResponsePrefix_preserves (c : AmbientContracts I) (sc : SocketContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (indexInsert owner)))
    (create : ∀ pid, PrefixPreserves I LifetimeEvent.Safe (keypairCreatePrefix pid))
    (put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (keypairPutPrefix kp now))
    (replace : ∀ pid kp, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (indexReplaceHandshake pid kp)))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (sendHandshakeResponsePrefix pid) := by
  unfold sendHandshakeResponsePrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (hiddenClock64_sameKernel _))
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact createResponsePrefix_preserves c hi _
    | with_reducible exact addMacToPacketPrefix_preserves c _ _
    | with_reducible exact beginSessionPrefix_preserves_ambient c create put replace _
    | with_reducible exact AmbientContracts.drop (timersSessionDerivedPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (timersTraversalPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (timersAnyAuthenticatedPacketSentPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (sendBufferToPeerPrefix_spec c sc (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem handshakeSendWorkerPrefix_preserves (c : AmbientContracts I) (sc : SocketContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (indexInsert owner)))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (handshakeSendWorkerPrefix pid) :=
  PrefixPreserves.bind (sendHandshakeInitiationPrefix_preserves c sc hi pid) (fun _ => c.peerPut _)

inductive HandshakeSendCall where
  | buffer (pid : PeerId) (bytes : List UInt8)
  | sessionDerived (pid : PeerId)
  | initiated (pid : PeerId)
  | initiation (pid : PeerId)
  | response (pid : PeerId)
  | worker (pid : PeerId)

namespace HandshakeSendCall

def original : HandshakeSendCall → M Unit
  | .buffer pid bytes => sendBufferToPeer pid bytes
  | .sessionDerived pid => timersSessionDerived pid
  | .initiated pid => timersHandshakeInitiated pid
  | .initiation pid => sendHandshakeInitiation pid
  | .response pid => sendHandshakeResponse pid
  | .worker pid => handshakeSendWorker pid

def observed : HandshakeSendCall → MixedM Unit
  | .buffer pid bytes => sendBufferToPeerPrefix pid bytes
  | .sessionDerived pid => timersSessionDerivedPrefix pid
  | .initiated pid => timersHandshakeInitiatedPrefix pid
  | .initiation pid => sendHandshakeInitiationPrefix pid
  | .response pid => sendHandshakeResponsePrefix pid
  | .worker pid => handshakeSendWorkerPrefix pid

theorem erases (call : HandshakeSendCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | buffer pid bytes => exact sendBufferToPeerPrefix_erases pid bytes
  | sessionDerived pid => exact timersSessionDerivedPrefix_erases pid
  | initiated pid => exact timersHandshakeInitiatedPrefix_erases pid
  | initiation pid => exact sendHandshakeInitiationPrefix_erases pid
  | response pid => exact sendHandshakeResponsePrefix_erases pid
  | worker pid => exact handshakeSendWorkerPrefix_erases pid

theorem preserves_ambient (c : AmbientContracts I) (sc : SocketContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (indexInsert owner)))
    (create : ∀ pid, PrefixPreserves I LifetimeEvent.Safe (keypairCreatePrefix pid))
    (put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (keypairPutPrefix kp now))
    (replace : ∀ pid kp, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (indexReplaceHandshake pid kp)))
    (call : HandshakeSendCall) : PrefixPreserves I LifetimeEvent.Safe call.observed := by
  cases call with
  | buffer pid bytes => exact AmbientContracts.drop (sendBufferToPeerPrefix_spec c sc (fun _ => True) pid bytes)
  | sessionDerived pid => exact AmbientContracts.drop (timersSessionDerivedPrefix_spec c (fun _ => True) pid)
  | initiated pid => exact AmbientContracts.drop (timersHandshakeInitiatedPrefix_spec c (fun _ => True) pid)
  | initiation pid => exact sendHandshakeInitiationPrefix_preserves c sc hi pid
  | response pid => exact sendHandshakeResponsePrefix_preserves c sc hi create put replace pid
  | worker pid => exact handshakeSendWorkerPrefix_preserves c sc hi pid

theorem allocation (call : HandshakeSendCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationSocket indexInsert_allocation
    keypairCreatePrefix_preserves keypairPutPrefix_allocation indexReplaceHandshake_allocation

end HandshakeSendCall
end Leanux.Proofs.WG.Lifetimes
