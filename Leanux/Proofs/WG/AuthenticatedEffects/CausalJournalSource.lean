import Leanux.Proofs.WG.TransmitSecurity.JournalSource
import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsMatching
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffectsNatural
import Leanux.Proofs.WG.AuthenticatedEffects.CausalSourceMetadata
import Leanux.Proofs.WG.AuthenticatedEffects.SendEffectsSource
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeJointWorker

/-! One final extension of the existing combined journal on the same native
Driver spine. The old event type is embedded intact. Causal scope metadata is
not authorization; missing contexts remain explicit in actual effect receipts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

abbrev Cause := CausalSources.Cause
abbrev Context := CausalEffects.Context Cause

inductive Event where
  | old (value : Journal.Event)
  | scope (value : CausalScope.Event Cause)
  | armed (value : TimerEffects.Arm Context)
  | queued (value : TimerEffects.Queued Context)
  | exchange (value : HandshakeSecurity.Exchange.Event)

def old? : Event → Option Journal.Event
  | .old value => some value
  | _ => none

def scope? : Event → Option (CausalScope.Event Cause)
  | .scope value => some value
  | _ => none

def arm? : Event → Option (TimerEffects.Arm Context)
  | .armed value => some value
  | _ => none

def queue? : Event → Option (TimerEffects.Queued Context)
  | .queued value => some value
  | _ => none

def exchange? : Event → Option HandshakeSecurity.Exchange.Event
  | .exchange value => some value
  | _ => none

def handshake? (event : Event) : Option HandshakeCausal.Event :=
  (old? event).bind Journal.handshake?

def completion? (event : Event) : Option Completion.Event :=
  (old? event).bind Journal.completion?

def effects : TimerEffects.Ops (WGPrefix Event) := CausalEffects.ops scope? Event.armed Event.queued

def state (body : WGPrefix Journal.Event α) : WGPrefix Event α :=
  focusStatePrefix Event.old old? body

def product (body : PrefixM Journal.Event α) : PrefixM Event α :=
  focusPrefix Event.old old? body

def session (pid : PeerId) : WGPrefix Event Bool :=
  HandshakeSecurity.ExchangeJoint.session Event.exchange pid (state (Journal.session pid))

def handshake (session : PeerId → WGPrefix Event Bool)
    (keepalive : PeerId → WGPrefix Event Unit) : WGPrefix Event Bool :=
  HandshakeWorker.observedWith fun mac =>
    HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
      (HandshakeSecurity.ExchangeJoint.receiveOps Event.exchange
        (HandshakeEffects.withEffects
          (HandshakeWorker.observedOps (Event.old ∘ Journal.Event.handshake) handshake? session keepalive mac)
          (Event.old ∘ Journal.Event.handshake) effects))

def flushedSend (pid : PeerId) : WGPrefix Event Unit :=
  SendEffects.flushed Event.scope
    (HandshakeSecurity.ExchangeJoint.sendOps Event.exchange SendEffects.native) effects pid

def transmit (pid : PeerId) : PrefixM Event Bool :=
  CompletionEffects.observedStep (Event.old ∘ Journal.completionEvent) completion?
    Event.scope scope? CausalSources.Cause.completion Event.armed Event.queued pid

def hooks : Driver.Hooks Event where
  fixtureEnter := (CausalSources.fixtureHooks Event.scope).enter
  fixtureLeave := (CausalSources.fixtureHooks Event.scope).leave
  handshake := handshake
  flushedSend := flushedSend
  armTimer := effects.arm
  queueSend := effects.append
  candidateEnter := CausalSources.candidateEnter Event.scope
  candidateLeave := CausalScope.leavePrefix Event.scope
  stackInput := fun entry body => CausalScope.prefixScope Event.scope (.stackInput entry) (fun _ => body)
  timerSelected := CausalSources.timerEnter Event.scope (Event.old ∘ Journal.Event.timerSelected)
  timerFinished := CausalScope.leavePrefix Event.scope
  prepare := product Journal.hooks.prepare
  counterCheck := fun skb packet => product (Journal.hooks.counterCheck skb packet)
  selection := fun pid => state (Journal.selection pid)
  confirmation := fun pid kid => state (Journal.confirmation pid kid)
  session := session
  reserve := fun slot => state (Journal.reserve slot)
  allocate := fun packets => state (Journal.allocate packets)
  create := fun pid item => state (Journal.create pid item)
  front := fun family addr packets mtu => state (Journal.front family addr packets mtu)
  poll := product Journal.poll
  encrypt := fun item => product (Journal.encrypt item)
  transmit := transmit

def execute (trace : Runner.Trace) (placeholders : Bool) : PrefixOuter Event Lean.Json :=
  Driver.executeObserved hooks trace placeholders

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal
