import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationTakeSource
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationRestoreObserved
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationTerminalObserved
import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalEncryptionFocus
import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalLifetimeProjection
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseAdmissionProjection
import Leanux.Proofs.WG.TransmitSecurity.JournalSource
import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsMatching
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeEffectsNatural
import Leanux.Proofs.WG.AuthenticatedEffects.CausalSourceMetadata
import Leanux.Proofs.WG.AuthenticatedEffects.SendEffectsSource
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeJointWorker
import Leanux.Proofs.WG.AuthenticatedEffects.ProtocolSenderOps
import Leanux.Proofs.WG.AuthenticatedEffects.CookieConsumptionSource
import Leanux.Proofs.WG.AuthenticatedEffects.DeliverySource
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationFrontObserved
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationSendResult
import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalDecorations

/-! One final extension of the existing combined journal on the same native
Driver spine. The old event type is embedded intact. Causal scope metadata is
not authorization; missing contexts remain explicit in actual effect receipts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

abbrev Cause := CausalSources.Cause
abbrev Context := CausalEffects.Context Cause

inductive Event where
  | stagingTaken (receipt : HandshakeSecurity.StagedConservation.Take.Receipt)
  | stagedRestored (receipt : HandshakeSecurity.StagedConservation.Restore.Receipt)
  | terminalDrop (receipt : HandshakeSecurity.StagedConservation.Terminal.Receipt)
  | transmitInput (input : HandshakeSecurity.StagedConservation.Front.Input)
  | stagedDisposal (event : HandshakeSecurity.StagedDisposal.Event)
  | sendResult (receipt : HandshakeSecurity.StagedConservation.SendResult.Receipt)
  | delivery (sent : List SentDatagram)
  | cookieConsumed (receipt : CookieConsumption.Receipt)
  | keepalivePrepared (pid : PeerId) (run : WGRunWitness Bool)
  | old (value : Journal.Event)
  | scope (value : CausalScope.Event Cause)
  | armed (value : TimerEffects.Arm Context)
  | queued (value : TimerEffects.Queued Context)
  | exchange (value : HandshakeSecurity.Exchange.Event)
  | protocolSocket (receipt : ProtocolSocket.Receipt Context)
  | cookieSocket (receipt : CookieSocket.Receipt)

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

def stagedDisposal? : Event → Option HandshakeSecurity.StagedDisposal.Event
  | .stagedDisposal value => some value
  | _ => none

def effects : TimerEffects.Ops (WGPrefix Event) := CausalEffects.ops scope? Event.armed Event.queued

def state (body : WGPrefix Journal.Event α) : WGPrefix Event α :=
  focusStatePrefix Event.old old? body

def product (body : PrefixM Journal.Event α) : PrefixM Event α :=
  focusPrefix Event.old old? body

def session (pid : PeerId) : WGPrefix Event Bool :=
  HandshakeSecurity.ExchangeJoint.session Event.exchange pid (state (Journal.session pid))

def receiveOps (session : PeerId → WGPrefix Event Bool)
    (keepalive : PeerId → WGPrefix Event Unit) (mac : HandshakeMac) :
    Origins.HandshakeSources.Ops (WGPrefix Event) :=
  {HandshakeSecurity.StagedDisposal.Decoration.receive Event.stagedDisposal stagedDisposal?
      (ProtocolSender.receiveOps (Event.old ∘ Journal.Event.handshake) handshake? session keepalive mac
        Event.protocolSocket scope? Event.cookieSocket) with
    initiation := fun msg => RetirementSecurity.NestedPeerRelease.admitInitiationWith
      (RetirementSecurity.NestedPeerRelease.observedOps Event.stagedDisposal stagedDisposal?)
      (Event.old ∘ Journal.Event.handshake ∘ HandshakeCausal.Event.admission) {mac with input := msg}
    response := fun msg => RetirementSecurity.NestedPeerRelease.admitResponseWith
      (RetirementSecurity.NestedPeerRelease.observedOps Event.stagedDisposal stagedDisposal?)
      (Event.old ∘ Journal.Event.handshake ∘ HandshakeCausal.Event.admission) {mac with input := msg}}

def handshake (session : PeerId → WGPrefix Event Bool)
    (keepalive : PeerId → WGPrefix Event Unit) : WGPrefix Event Bool :=
  CookieConsumption.workerWith
    (RetirementSecurity.NestedPeerRelease.cookieObserved
      (RetirementSecurity.NestedPeerRelease.observedOps Event.stagedDisposal stagedDisposal?) Event.cookieConsumed) fun mac =>
    HandshakeEffects.scopeOps Event.scope CausalSources.Cause.handshake
      (HandshakeSecurity.ExchangeJoint.receiveOps Event.exchange
        (HandshakeEffects.withEffects
          (receiveOps session keepalive mac)
          (Event.old ∘ Journal.Event.handshake) effects))

def flushedSend (pid : PeerId) : WGPrefix Event Unit :=
  SendEffects.flushed Event.scope
    (HandshakeSecurity.ExchangeJoint.sendOps Event.exchange
      (HandshakeSecurity.StagedDisposal.Decoration.send Event.stagedDisposal stagedDisposal?
        (ProtocolSender.sendOps Event.protocolSocket scope?))) effects pid

def txEvent (event : Queues.TxDisposition.Event) : Event := .old (.disposition event)

def txEvent? (event : Event) : Option Queues.TxDisposition.Event :=
  (old? event).bind Journal.disposition?

def completionLifetime : LifetimeEffects.Ops (WGPrefix Event) :=
  HandshakeSecurity.StagedDisposal.LifetimeSource.decorate
    (Event.old ∘ Journal.completionEvent) completion? scope? Event.armed Event.queued Event.stagedDisposal

def completionOps : CompletionEffects.Ops Event :=
  {HandshakeSecurity.StagedConservation.SendResult.decorate Event.sendResult
    (CompletionEffects.observed (Event.old ∘ Journal.completionEvent) completion?
      scope? Event.armed Event.queued) with
    fresh := fun pid => liftWGObserver (LifetimeEffects.freshWith completionLifetime pid)
    dispose := HandshakeSecurity.StagedDisposal.TxSource.dispose
      (HandshakeSecurity.StagedDisposal.TxSource.observed txEvent txEvent? Event.stagedDisposal)}

def transmit (pid : PeerId) : PrefixM Event Bool :=
  HandshakeSecurity.StagedConservation.Terminal.stepWith completionOps
    (CompletionEffects.completeScoped Event.scope CausalSources.Cause.completion completionOps)
    (HandshakeSecurity.StagedConservation.Terminal.deadObserved txEvent txEvent?
      Event.stagedDisposal Event.terminalDrop) pid

def selection (pid : PeerId) : WGPrefix Event (Option (Peer × Option KeypairId)) :=
  HandshakeSecurity.StagedConservation.Take.selection Event.stagingTaken
    (fun pid run => .old (.responder (.selected pid run))) pid

def stagedRestore (pid : PeerId) (packets : List Packet) : WGPrefix Event Unit :=
  HandshakeSecurity.StagedConservation.Restore.observed Event.stagedRestored pid packets

def create (pid : PeerId) (item : List SkbId) : WGPrefix Event Unit :=
  NativeAdapter.lower (HandshakeSecurity.StagedConservation.Terminal.createObserved
    txEvent txEvent? Event.stagedDisposal Event.terminalDrop pid item)

def encrypt (item : Option (List SkbId)) : PrefixM Event Bool :=
  receiptObserved (HandshakeSecurity.StagedDisposal.EncryptionSource.tail
    (HandshakeSecurity.StagedDisposal.EncryptionSource.observed
      (Event.old ∘ Journal.Event.encrypted) (fun event => (old? event).bind Journal.encryption?)
      Event.stagedDisposal stagedDisposal?) item) (fun run => .old (.encryptionReturn item run))

def front (family addr : Nat) (packets : List Packet) (mtu : Nat) : WGPrefix Event (Except Int PeerId) :=
  HandshakeSecurity.StagedConservation.Front.observed Event.transmitInput Event.stagedDisposal stagedDisposal?
    (fun input run => .old (.routed input.family input.address input.packets input.mtu run))
    ⟨family,addr,packets,mtu⟩

def stagedPurge (pid : PeerId) : WGPrefix Event Unit :=
  focusStatePrefix Event.stagedDisposal stagedDisposal? (HandshakeSecurity.StagedDisposal.purgeObserved pid)

def peerRelease (peer : Option PeerId) : WGPrefix Event Unit :=
  HandshakeSecurity.StagedDisposal.Decoration.release Event.stagedDisposal stagedDisposal? peer

def keepalivePrepare (pid : PeerId) : WGPrefix Event Bool :=
  receiptWGObserved (liftWGPrefix (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid))
    (.keepalivePrepared pid)

def hooks : Driver.Hooks Event where
  stagedRestore := stagedRestore
  stagedPurge := stagedPurge
  peerRelease := peerRelease
  deliver := DeliverySource.observed Event.delivery
  keepalivePrepare := keepalivePrepare
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
  selection := selection
  confirmation := fun pid kid => state (Journal.confirmation pid kid)
  session := session
  reserve := fun slot => state (Journal.reserve slot)
  allocate := fun packets => state (Journal.allocate packets)
  create := create
  front := front
  poll := product Journal.poll
  encrypt := encrypt
  transmit := transmit

def execute (trace : Runner.Trace) (placeholders : Bool) : PrefixOuter Event Lean.Json :=
  Driver.executeObserved hooks trace placeholders

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal
