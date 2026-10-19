import Leanux.Proofs.WG.AuthenticatedEffects.CausalEffects
import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsNeutral
import Leanux.Proofs.WG.TransmitSecurity.CompletionEmission

/-! The original protocol-buffer sender exposes each native socket call before
later peer accounting. Its receipt survives a Stop after an emitted datagram;
observing only the completed buffer sender would lose that prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSocket
open Leanux Leanux.WG Leanux.Proofs.Logged

structure Args where
  ipv4 : Bool
  endpoint : Endpoint
  cache : Option PeerId
  bytes : List UInt8
  ds : Nat
  exactRx : Bool

def Args.action (args : Args) : WG.M Int :=
  if args.ipv4 then send4 args.endpoint args.cache args.bytes args.ds args.exactRx
  else send6 args.endpoint args.cache args.bytes args.ds args.exactRx

structure Receipt (Context : Type) where
  cause : Context
  args : Args
  run : WGRunWitness Int

def Receipt.Valid (receipt : Receipt Context) : Prop := receipt.run.Valid receipt.args.action

def bufferWith {m : Type → Type} [Monad m]
    (step : {α : Type} → WG.M α → m α) (socket : Args → m Int)
    (pid : PeerId) (bytes : List UInt8) : m Unit := do
  if ← step (branch .sendBufNoMem !(← step (hiddenAlloc .sendBufSkb))) then return
  let peer ← step (getPeer pid)
  let family := (peer.endpoint.map (·.family)).getD 0
  let endpoint := peer.endpoint.getD {family := 0,addr := 0,port := 0}
  let ret ← do
    if ← step (branch .sendSkbInet (family == AF_INET)) then
      socket ⟨true,endpoint,some pid,bytes,HANDSHAKE_DSCP,true⟩
    else if ← step (branch .sendSkbInet6 (family == AF_INET6)) then
      socket ⟨false,endpoint,some pid,bytes,HANDSHAKE_DSCP,true⟩
    else pure (-EAFNOSUPPORT)
  if ← step (branch .sendSkbOk (ret == 0)) then
    let peer ← step (getPeer pid)
    step (setPeer pid {peer with txBytes := peer.txBytes + bytes.length})

theorem buffer_factor (pid : PeerId) (bytes : List UInt8) :
    bufferWith (fun action => action) Args.action pid bytes = sendBufferToPeer pid bytes := rfl

/-- Each receipt describes the actual native socket return before any later
buffer accounting. A callback's context is supplied separately by its caller. -/
def socket (record : Receipt Context → E) (context : Context) (args : Args) : WGPrefix E Int :=
  receiptWGObserved (liftWGPrefix args.action) (fun run => record ⟨context,args,run⟩)

def observed (record : Receipt (CausalEffects.Context Cause) → E)
    (scope : E → Option (CausalScope.Event Cause)) (pid : PeerId) (bytes : List UInt8) : WGPrefix E Unit :=
  bufferWith liftWGPrefix (fun args => CausalEffects.atCurrent scope fun context => socket record context args) pid bytes

theorem Receipt.Valid.emission {receipt : Receipt Context} (valid : receipt.Valid) :
    SocketEmission receipt.args.endpoint receipt.args.bytes receipt.args.ds receipt.run.before.sent receipt.run.after.sent := by
  have run := valid
  unfold Receipt.Valid Args.action at run
  cases flag : receipt.args.ipv4 with
  | false =>
    simp only [flag, Bool.false_eq_true, ite_false] at run
    exact TransmitSecurity.Completion.send6_emission _ _ _ _ _ _ _ _ _ _ run
  | true =>
    simp only [flag, ite_true] at run
    exact TransmitSecurity.Completion.send4_emission _ _ _ _ _ _ _ _ _ _ run

end Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSocket
