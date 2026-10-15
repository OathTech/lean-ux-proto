import Leanux.Proofs.WG.TimerDiscipline.Model

/-! Exact ordered retry-callback updates and decisions. Readiness is stated on
entry fields and supplied records, including the registered send-work identity. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.RetryReady
open Leanux Leanux.WG Campaign2

def word (bytes : List UInt8) : UInt64 :=
  (bytes.foldr (fun (b : UInt8) (acc : Nat) => acc * 256 + b.toNat) 0).toUInt64
def bumped (p : Peer) : Peer := {p with timerHandshakeAttempts := p.timerHandshakeAttempts+1}
def cleared (p : Peer) : Peer := {(bumped p) with endpoint := p.endpoint.map fun e => {e with src:=0,srcIf:=0}}
def reset (p : Peer) (bs : List UInt8) : Peer := {(cleared p) with dstCache := {(cleared p).dstCache with resetTs := word bs}}
def dropped (p : Peer) (bs : List UInt8) : Peer := {(reset p bs) with dstCache := {(reset p bs).dstCache with slot := none}}
def acquired (p : Peer) (bs : List UInt8) : Peer := {(dropped p bs) with refcount:=p.refcount+1}
def queued (p : Peer) (bs : List UInt8) : Peer := {(acquired p bs) with handshakePending := true}
def result (d : Device) (pid : PeerId) (p : Peer) (bs : List UInt8) : Device :=
  {d with peers := (((((d.peers.insert pid (bumped p)).insert pid (cleared p)).insert pid (reset p bs)).insert pid (dropped p bs)).insert pid (acquired p bs)).insert pid (queued p bs)
          sendWorkQueue := d.sendWorkQueue ++ [pid]}
def decisions (p : Peer) (clock : List UInt8) (netRx : Nat) (steps : Array Step) :=
  let lhs := p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64
  ((((((((steps.push {decision:=.retransmitGiveUp,outcome:=false,operands:=some (p.timerHandshakeAttempts,MAX_TIMER_HANDSHAKES),netRx}).push
    {decision:=.queuedNotRetry,outcome:=false,netRx}).push
    {decision:=.queuedNotExpired,outcome:=false,operands:=some (lhs.toInt,(word clock).toInt64.toInt),netRx}).push
    {decision:=.queuedDead,outcome:=false,netRx}).push
    {decision:=.refcountAddFromZero,outcome:=false,operands:=some (p.refcount,0),netRx}).push
    {decision:=.refcountAddNegative,outcome:=false,netRx}).push
    {decision:=.refcountAddWraps,outcome:=false,netRx}).push
    {decision:=.queuedAlreadyQueued,outcome:=false,netRx})

def callbackView (entry : Snapshot) (d : Device) (pid : PeerId) (p : Peer)
    (cache clock : List UInt8) (rest : List HiddenRecord) : Snapshot :=
  {entry with
    wg := {entry.wg with
      device := some (result d pid p cache)
      queuedThisCall := pid :: entry.wg.queuedThisCall}
    ambient := {entry.ambient with
      hidden := some rest
      steps := decisions p clock entry.ambient.netRxSection entry.ambient.steps}}

end Leanux.Proofs.WG.TimerDiscipline.RetryReady
