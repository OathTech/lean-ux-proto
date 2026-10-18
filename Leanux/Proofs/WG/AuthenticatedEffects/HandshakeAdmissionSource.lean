import Leanux.Proofs.WG.AuthenticatedEffects.InitiationAcceptance
import Leanux.Proofs.WG.AuthenticatedEffects.ResponseAcceptance
import Leanux.Proofs.WG.Origins.HandshakeSources
import Leanux.Proofs.WG.KeyTimes.ReceiveAttempts

/-! The original handshake receiver with actual MAC and pre-write Noise
acceptance receipts. Every native callback and refusal arm is retained. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged
open Origins.HandshakeSources
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

structure HandshakeMac where
  input : Key
  source : SkbSource
  loaded : Bool
  checked : WGRunWitness MacState

def HandshakeMac.Valid (r : HandshakeMac) : Prop :=
  r.checked.Valid (cookieValidatePacket r.input r.source r.loaded) ∧
    r.checked.value = authenticatedMac r.loaded

inductive HandshakeAdmission where
  | initiation (mac : HandshakeMac) (checked : WGRunWitness (Option AcceptedInitiation))
  | response (mac : HandshakeMac) (checked : WGRunWitness (Option AcceptedResponse))

def HandshakeAdmission.Valid : HandshakeAdmission → Prop
  | .initiation mac checked => mac.Valid ∧ checked.Valid (initiationAcceptedCheck mac.input) ∧ checked.value.isSome = true
  | .response mac checked => mac.Valid ∧ checked.Valid (responseAcceptedCheck mac.input) ∧ checked.value.isSome = true

def admitInitiation (mac : HandshakeMac) : WGPrefix HandshakeAdmission (Option PeerId) := do
  let checked ← captureWGRun (initiationAcceptedCheck mac.input)
  if checked.value.isSome then emitStatePrefix (.initiation mac checked)
  liftWGPrefix (initiationAcceptedContinue mac.input checked.value)

def admitResponse (mac : HandshakeMac) : WGPrefix HandshakeAdmission (Option PeerId) := do
  let checked ← captureWGRun (responseAcceptedCheck mac.input)
  if checked.value.isSome then emitStatePrefix (.response mac checked)
  liftWGPrefix (responseAcceptedContinue mac.input checked.value)

private theorem emit_lift (e : HandshakeAdmission) (a : WG.M α) :
    ErasesStatePrefix (do emitStatePrefix e; liftWGPrefix a) a := by
  intro w ambient h
  change (runStatePrefix (do emitStatePrefix e; liftWGPrefix a) w ambient h).1 = _
  simp only [runStatePrefix_bind,runStatePrefix_emit,liftWGPrefix,runStatePrefix_lift]

theorem admitInitiation_erases (mac : HandshakeMac) :
    ErasesStatePrefix (admitInitiation mac) (consumeInitiation mac.input) := by
  rw [←initiationAcceptedCheck_factor]
  unfold admitInitiation
  apply KeyTimes.captureWGRun_bind_erases
  intro checked
  split
  · exact emit_lift _ _
  · exact erasesStatePrefix_lift _

theorem admitResponse_erases (mac : HandshakeMac) :
    ErasesStatePrefix (admitResponse mac) (consumeResponse mac.input) := by
  rw [←responseAcceptedCheck_factor]
  unfold admitResponse
  apply KeyTimes.captureWGRun_bind_erases
  intro checked
  split
  · exact emit_lift _ _
  · exact erasesStatePrefix_lift _

def admissionOps (mac : HandshakeMac) : Ops (WGPrefix HandshakeAdmission) where
  step := liftWGPrefix
  session := fun pid => liftWGPrefix (beginSession pid)
  modifyPeer := fun pid f => liftWGPrefix (do setPeer pid (f (← getPeer pid)))
  create := fun pid => liftWGPrefix (createResponse pid)
  mac := fun pid msg => liftWGPrefix (addMacToPacket pid msg)
  send := fun pid msg => liftWGPrefix (sendBufferToPeer pid msg)
  derived := fun pid => liftWGPrefix (timersSessionDerived pid)
  traversal := fun pid => liftWGPrefix (timersTraversal pid)
  sent := fun pid => liftWGPrefix (timersAnyAuthenticatedPacketSent pid)
  cookie := fun msg src => liftWGPrefix (sendHandshakeCookie msg src)
  initiation := fun msg => admitInitiation {mac with input := msg}
  response := fun msg => admitResponse {mac with input := msg}
  endpoint := fun pid src => liftWGPrefix (setPeerEndpointFromSkb pid src)
  complete := fun pid => liftWGPrefix (timersHandshakeComplete pid)
  keepalive := fun pid => liftWGPrefix (sendKeepalive pid)
  received := fun pid => liftWGPrefix (timersAnyAuthenticatedPacketReceived pid)
  put := fun peer => liftWGPrefix (WG.peerPut peer)
  cookieConsume := fun msg => liftWGPrefix (cookieMessageConsume msg)

def receiveAdmissions (msg : Key) (src : SkbSource) : WGPrefix HandshakeAdmission Unit := do
  if ← liftWGPrefix (branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE)) then
    liftWGPrefix (cookieMessageConsume msg)
    return
  let loaded ← liftWGPrefix Cookies.loadPhase
  let checked ← captureWGRun (cookieValidatePacket msg src loaded)
  afterMacWith (admissionOps ⟨msg,src,loaded,checked⟩) msg src loaded checked.value

private theorem lift_erases (a : WG.M α) :
    ErasesStatePrefix (liftWGPrefix a : WGPrefix HandshakeAdmission α) a :=
  erasesStatePrefix_lift a

private theorem erases_choice (p : Prop) [Decidable p]
    (a b : WGPrefix HandshakeAdmission α) (c d : WG.M α)
    (ha : ErasesStatePrefix a c) (hb : ErasesStatePrefix b d) :
    ErasesStatePrefix (if p then a else b) (if p then c else d) := by
  split <;> assumption

elab "admission_erases_choice" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``ErasesStatePrefix do
    Lean.throwError "expected an erasure contract"
  let args := target.getAppArgs
  let observed := args[args.size - 2]!
  unless observed.isAppOf ``ite do
    Lean.throwError "expected an explicit choice"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply erases_choice))

theorem responseWith_admission_erases (mac : HandshakeMac) (pid : PeerId) :
    ErasesStatePrefix (responseWith (admissionOps mac) pid) (responseWith original pid) := by
  unfold responseWith
  simp only [admissionOps,original]
  repeat' first
    | with_reducible exact lift_erases _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | split
    | admission_erases_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only [Option.some.injEq]

elab "admission_response_erases" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``ErasesStatePrefix do
    Lean.throwError "expected an erasure contract"
  let args := target.getAppArgs
  let observed := args[args.size - 2]!
  unless observed.isAppOf ``responseWith do
    Lean.throwError "expected the response sender"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact responseWith_admission_erases _ _))

theorem afterMac_admission_erases (mac : HandshakeMac) (msg : Key) (src : SkbSource)
    (loaded : Bool) (state : MacState) :
    ErasesStatePrefix (afterMacWith (admissionOps mac) msg src loaded state)
      (afterMacWith original msg src loaded state) := by
  unfold afterMacWith
  simp only [admissionOps,original]
  repeat' first
    | admission_response_erases
    | with_reducible exact admitInitiation_erases _
    | with_reducible exact admitResponse_erases _
    | with_reducible exact lift_erases _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | split
    | admission_erases_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only [Option.some.injEq]

theorem receiveAdmissions_erases (msg : Key) (src : SkbSource) :
    ErasesStatePrefix (receiveAdmissions msg src) (receiveHandshakePacket msg src) := by
  rw [←reception_original]
  unfold receiveAdmissions receptionWith
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro cookie
  split
  · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro doneUnit
    exact erasesStatePrefix_pure _
  · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro loaded
    apply KeyTimes.captureWGRun_bind_erases
    intro checked
    exact afterMac_admission_erases _ _ _ _ _

end Leanux.Proofs.WG.AuthenticatedEffects
