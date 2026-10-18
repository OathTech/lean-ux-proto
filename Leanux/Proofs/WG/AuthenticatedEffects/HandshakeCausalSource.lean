import Leanux.Proofs.WG.AuthenticatedEffects.AdmissionCompletion

/-! Callback entries of the actual handshake receiver. A callback receipt is
emitted before the native operation, so effects before a later Stop remain
inside the recorded call. Reference accounting and the cookie exception retain
their separate source paths. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeCausal
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

inductive Kind where
  | session | peerWrite | responseCreate | outgoingMac | send | sessionDerived
  | traversal | authenticatedSent | endpoint | handshakeComplete | keepalive | authenticatedReceived

inductive Event where
  | admission (receipt : HandshakeAdmission)
  | callback (kind : Kind) (peer : PeerId)

def admission : Event → Option HandshakeAdmission
  | .admission r => some r
  | .callback _ _ => none

def call (kind : Kind) (peer : PeerId) (action : WG.M α) : WGPrefix Event α := do
  emitStatePrefix (.callback kind peer)
  liftWGPrefix action

def initiation (mac : HandshakeMac) : WGPrefix Event (Option PeerId) :=
  focusStatePrefix .admission admission (admitInitiation mac)
def response (mac : HandshakeMac) : WGPrefix Event (Option PeerId) :=
  focusStatePrefix .admission admission (admitResponse mac)

theorem call_erases (kind : Kind) (peer : PeerId) (action : WG.M α) :
    ErasesStatePrefix (call kind peer action) action := by
  intro w a h
  change (runStatePrefix (do emitStatePrefix (.callback kind peer); liftWGPrefix action) w a h).1 = _
  simp only [runStatePrefix_bind,runStatePrefix_emit,liftWGPrefix,runStatePrefix_lift]

theorem initiation_erases (mac : HandshakeMac) :
    ErasesStatePrefix (initiation mac) (consumeInitiation mac.input) :=
  focusStatePrefix_erases _ _ (admitInitiation_erases mac)
theorem response_erases (mac : HandshakeMac) :
    ErasesStatePrefix (response mac) (consumeResponse mac.input) :=
  focusStatePrefix_erases _ _ (admitResponse_erases mac)

def ops (mac : HandshakeMac) : Ops (WGPrefix Event) where
  step := liftWGPrefix
  session := fun pid => call .session pid (beginSession pid)
  modifyPeer := fun pid f => call .peerWrite pid (do setPeer pid (f (← getPeer pid)))
  create := fun pid => call .responseCreate pid (createResponse pid)
  mac := fun pid msg => call .outgoingMac pid (addMacToPacket pid msg)
  send := fun pid msg => call .send pid (sendBufferToPeer pid msg)
  derived := fun pid => call .sessionDerived pid (timersSessionDerived pid)
  traversal := fun pid => call .traversal pid (timersTraversal pid)
  sent := fun pid => call .authenticatedSent pid (timersAnyAuthenticatedPacketSent pid)
  cookie := fun msg src => liftWGPrefix (sendHandshakeCookie msg src)
  initiation := fun msg => initiation {mac with input := msg}
  response := fun msg => response {mac with input := msg}
  endpoint := fun pid src => call .endpoint pid (setPeerEndpointFromSkb pid src)
  complete := fun pid => call .handshakeComplete pid (timersHandshakeComplete pid)
  keepalive := fun pid => call .keepalive pid (sendKeepalive pid)
  received := fun pid => call .authenticatedReceived pid (timersAnyAuthenticatedPacketReceived pid)
  put := fun peer => liftWGPrefix (WG.peerPut peer)
  cookieConsume := fun msg => liftWGPrefix (cookieMessageConsume msg)

def receive (msg : Key) (src : SkbSource) : WGPrefix Event Unit := do
  if ← liftWGPrefix (branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE)) then
    liftWGPrefix (cookieMessageConsume msg)
    return
  let loaded ← liftWGPrefix Cookies.loadPhase
  let checked ← captureWGRun (cookieValidatePacket msg src loaded)
  afterMacWith (ops ⟨msg,src,loaded,checked⟩) msg src loaded checked.value

private theorem lift_erases (a : WG.M α) :
    ErasesStatePrefix (liftWGPrefix a : WGPrefix Event α) a := erasesStatePrefix_lift a
private theorem erases_choice (p : Prop) [Decidable p]
    (a b : WGPrefix Event α) (c d : WG.M α)
    (ha : ErasesStatePrefix a c) (hb : ErasesStatePrefix b d) :
    ErasesStatePrefix (if p then a else b) (if p then c else d) := by split <;> assumption

elab "causal_erases_choice" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``ErasesStatePrefix do Lean.throwError "expected an erasure contract"
  let args := target.getAppArgs
  unless args[args.size - 2]!.isAppOf ``ite do Lean.throwError "expected an explicit choice"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply erases_choice))

theorem responseWith_erases (mac : HandshakeMac) (pid : PeerId) :
    ErasesStatePrefix (responseWith (ops mac) pid) (responseWith original pid) := by
  unfold responseWith
  simp only [ops,original]
  repeat' first
    | with_reducible exact call_erases _ _ _
    | with_reducible exact lift_erases _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | split
    | causal_erases_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only [Option.some.injEq]

elab "causal_response_erases" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``ErasesStatePrefix do Lean.throwError "expected an erasure contract"
  let args := target.getAppArgs
  unless args[args.size - 2]!.isAppOf ``responseWith do Lean.throwError "expected the response sender"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact responseWith_erases _ _))

theorem afterMac_erases (mac : HandshakeMac) (msg : Key) (src : SkbSource)
    (loaded : Bool) (state : MacState) :
    ErasesStatePrefix (afterMacWith (ops mac) msg src loaded state)
      (afterMacWith original msg src loaded state) := by
  unfold afterMacWith
  simp only [ops,original]
  repeat' first
    | causal_response_erases
    | with_reducible exact initiation_erases _
    | with_reducible exact response_erases _
    | with_reducible exact call_erases _ _ _
    | with_reducible exact lift_erases _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | split
    | causal_erases_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only [Option.some.injEq]

theorem receive_erases (msg : Key) (src : SkbSource) :
    ErasesStatePrefix (receive msg src) (receiveHandshakePacket msg src) := by
  rw [←reception_original]
  unfold receive receptionWith
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
    exact afterMac_erases _ _ _ _ _

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeCausal
