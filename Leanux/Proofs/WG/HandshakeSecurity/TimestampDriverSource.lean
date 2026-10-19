import Leanux.Proofs.WG.HandshakeSecurity.WorkerClaims
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryOuter
import Leanux.Proofs.WG.TransmitSecurity.DriverOuterProjection
import Leanux.Proofs.WG.TransmitSecurity.DriverNeutralCalls

/-! Committed timestamp writes on the common native driver. The handshake
worker keeps its actual session and keepalive callbacks, including staging
inside those callbacks; only the timestamp write gains a receipt. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampDriver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Packets TransmitSecurity
open Origins.HandshakeSources

def ops (session : PeerId → WGPrefix TimestampReceipt Bool)
    (keepalive : PeerId → WGPrefix TimestampReceipt Unit) : Ops (WGPrefix TimestampReceipt) :=
  { Worker.ops with session, keepalive }

def worker (session : PeerId → WGPrefix TimestampReceipt Bool)
    (keepalive : PeerId → WGPrefix TimestampReceipt Unit) : WGPrefix TimestampReceipt Bool :=
  stepWith (ops session keepalive)

def hooks : Driver.Hooks TimestampReceipt where
  handshake := worker
  timerSelected := fun _ _ _ _ _ => pure 0
  selection := fun pid => liftWGPrefix (Responder.selectionPrefix pid)
  confirmation := fun pid kid => liftWGPrefix (receivedWithKeypair pid kid)
  session := fun pid => liftWGPrefix (beginSession pid)
  reserve := fun kid => liftWGPrefix (Nonce.reserveNative kid)
  allocate := fun packets => liftWGPrefix (packets.mapM newTxSkb)
  create := fun pid item => liftWGPrefix (createData pid item)
  front := fun family addr packets mtu => liftWGPrefix (txFront family addr packets mtu)
  poll := liftPrefix (liftWG TxRing.pollSource)
  encrypt := fun item => liftPrefix (RxWorkers.encryptStepTailSource item)
  transmit := fun pid => liftPrefix (liftWG (txStep pid))

def execute (trace : Runner.Trace) (placeholders : Bool) : PrefixOuter TimestampReceipt Lean.Json :=
  Driver.executeObserved hooks trace placeholders

macro "timestamp_driver_step" : tactic => `(tactic| first
  | (driver_history_head consumeObserved; exact consume_increasing _)
  | driver_state_history_step)

open Lean Meta Elab Tactic in
elab "timestamp_callback " source:ident " using " proof:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Driver.StateHistorySafe do throwError "not a history contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let .fvar fn := action.getAppFn | throwError "not a callback"
  unless (← fn.getDecl).userName.eraseMacroScopes == source.getId.eraseMacroScopes do
    throwError "different callback"
  evalTactic (← `(tactic| exact $proof _))

private theorem response_safe
    (session : PeerId → WGPrefix TimestampReceipt Bool)
    (keepalive : PeerId → WGPrefix TimestampReceipt Unit)
    (hs : ∀ pid, Driver.StateHistorySafe IncreasingReceipts (session pid))
    (pid : PeerId) :
    Driver.StateHistorySafe IncreasingReceipts (responseWith (ops session keepalive) pid) := by
  unfold responseWith
  simp only [ops,Worker.ops]
  repeat' first
    | timestamp_callback session using hs
    | timestamp_driver_step

private theorem after_mac_safe
    (session : PeerId → WGPrefix TimestampReceipt Bool)
    (keepalive : PeerId → WGPrefix TimestampReceipt Unit)
    (hs : ∀ pid, Driver.StateHistorySafe IncreasingReceipts (session pid))
    (hk : ∀ pid, Driver.StateHistorySafe IncreasingReceipts (keepalive pid))
    (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    Driver.StateHistorySafe IncreasingReceipts (afterMacWith (ops session keepalive) msg src loaded mac) := by
  unfold afterMacWith
  simp only [ops,Worker.ops]
  repeat' first
    | (driver_history_head responseWith; exact response_safe session keepalive hs _)
    | timestamp_callback session using hs
    | timestamp_callback keepalive using hk
    | timestamp_driver_step

private theorem reception_safe
    (session : PeerId → WGPrefix TimestampReceipt Bool)
    (keepalive : PeerId → WGPrefix TimestampReceipt Unit)
    (hs : ∀ pid, Driver.StateHistorySafe IncreasingReceipts (session pid))
    (hk : ∀ pid, Driver.StateHistorySafe IncreasingReceipts (keepalive pid))
    (msg : List UInt8) (src : SkbSource) :
    Driver.StateHistorySafe IncreasingReceipts (receptionWith (ops session keepalive) msg src) := by
  unfold receptionWith
  simp only [ops,Worker.ops]
  repeat' first
    | (driver_history_head afterMacWith; exact after_mac_safe session keepalive hs hk _ _ _ _)
    | timestamp_driver_step

theorem worker_safe
    (session : PeerId → WGPrefix TimestampReceipt Bool)
    (keepalive : PeerId → WGPrefix TimestampReceipt Unit)
    (hs : ∀ pid, Driver.StateHistorySafe IncreasingReceipts (session pid))
    (hk : ∀ pid, Driver.StateHistorySafe IncreasingReceipts (keepalive pid)) :
    Driver.StateHistorySafe IncreasingReceipts (worker session keepalive) := by
  unfold worker stepWith
  simp only [ops,Worker.ops]
  repeat' first
    | (driver_history_head receptionWith; exact reception_safe session keepalive hs hk _ _)
    | timestamp_driver_step

theorem hooks_safe : Driver.HooksHistorySafe IncreasingReceipts hooks where
  stagedRestore := fun _ _ => TransmitSecurity.Driver.History.state_lift _
  stagedPurge := fun _ => Leanux.Proofs.WG.TransmitSecurity.Driver.History.state_lift _
  peerRelease := fun _ => Leanux.Proofs.WG.TransmitSecurity.Driver.History.state_lift _
  deliver := Driver.History.product_lift _
  keepalivePrepare := fun _ => TransmitSecurity.Driver.History.state_lift _
  handshake := worker_safe
  fixtureEnter := fun _ => Driver.History.state_pure _
  fixtureLeave := fun _ => Driver.History.state_pure _
  sendWorker := by
    rw [Driver.sendWorker_lift hooks rfl]
    exact Driver.History.product_lift _
  armTimer := fun _ _ _ _ => Driver.History.state_lift _
  queueSend := fun _ => Driver.History.state_lift _
  flushedSend := fun _ => Driver.History.state_lift _
  candidateEnter := fun _ _ => Driver.History.product_pure _
  candidateLeave := fun _ => Driver.History.product_pure _
  stackInput := fun _ _ preserves => preserves
  prepare := Driver.History.product_lift _
  counterCheck := fun _ _ => Driver.History.product_state (Driver.History.state_lift _)
  timerSelected := fun _ _ _ _ _ => Driver.History.product_pure _
  timerFinished := fun _ => Driver.History.product_pure _
  selection := fun _ => Driver.History.state_lift _
  confirmation := fun _ _ => Driver.History.state_lift _
  session := fun _ => Driver.History.state_lift _
  reserve := fun _ => Driver.History.state_lift _
  allocate := fun _ => Driver.History.state_lift _
  create := fun _ _ => Driver.History.state_lift _
  front := fun _ _ _ _ => Driver.History.state_lift _
  poll := Driver.History.product_lift _
  encrypt := fun _ => Driver.History.product_lift _
  transmit := fun _ => Driver.History.product_lift _

theorem initialized_increasing (trace : Runner.Trace) (placeholders : Bool) :
    IncreasingReceipts (runPrefixOuter (execute trace placeholders) []).2 :=
  Driver.initialized_history hooks_safe (by intro r impossible; cases impossible) trace placeholders

end Leanux.Proofs.WG.HandshakeSecurity.TimestampDriver
