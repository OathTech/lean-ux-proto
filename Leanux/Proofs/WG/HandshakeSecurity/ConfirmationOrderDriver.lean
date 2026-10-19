import Leanux.Proofs.WG.TransmitSecurity.GroConfirmationOrder
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationOrderQuiet
import Leanux.Proofs.WG.AuthenticatedEffects.CandidateOrder

/-! Source wrappers for confirmation ordering. The temporary neutral
confirmation hook below is used only where it is definitionally absent from
the source. The real receive poll uses its accepted-counter contract. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity Driver
open Confirmation.Poll
variable {E : Type} {Good : List E → Prop} {hooks : Driver.Hooks E}

structure QuietHooksSafe (Good : List E → Prop) (hooks : Driver.Hooks E) : Prop where
  stagedPurge : ∀ pid, StateHistorySafe Good (hooks.stagedPurge pid)
  peerRelease : ∀ peer, StateHistorySafe Good (hooks.peerRelease peer)
  deliver : ProductHistorySafe Good hooks.deliver
  keepalivePrepare : ∀ pid, StateHistorySafe Good (hooks.keepalivePrepare pid)
  handshake : ∀ (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit),
    (∀ pid, StateHistorySafe Good (session pid)) →
    (∀ pid, StateHistorySafe Good (keepalive pid)) →
    StateHistorySafe Good (hooks.handshake session keepalive)
  fixtureEnter : ∀ trigger, StateHistorySafe Good (hooks.fixtureEnter trigger)
  fixtureLeave : ∀ token, StateHistorySafe Good (hooks.fixtureLeave token)
  sendWorker : ProductHistorySafe Good (Driver.sendWorkerObserved hooks)
  armTimer : ∀ pid timer delay caller, StateHistorySafe Good (hooks.armTimer pid timer delay caller)
  queueSend : ∀ pid, StateHistorySafe Good (hooks.queueSend pid)
  flushedSend : ∀ pid, StateHistorySafe Good (hooks.flushedSend pid)
  candidateEnter : ∀ skb pkt, ProductHistorySafe Good (hooks.candidateEnter skb pkt)
  candidateLeave : ∀ token, ProductHistorySafe Good (hooks.candidateLeave token)
  stackInput : ∀ entry body, ProductHistorySafe Good body →
    ProductHistorySafe Good (hooks.stackInput entry body)
  prepare : ProductHistorySafe Good hooks.prepare
  counterCheck : ∀ skb pkt, ProductHistorySafe Good (hooks.counterCheck skb pkt)
  timerSelected : ∀ d j pid t we, ProductHistorySafe Good (hooks.timerSelected d j pid t we)
  timerFinished : ∀ token, ProductHistorySafe Good (hooks.timerFinished token)
  selection : ∀ pid, StateHistorySafe Good (hooks.selection pid)
  session : ∀ pid, StateHistorySafe Good (hooks.session pid)
  reserve : ∀ kid, StateHistorySafe Good (hooks.reserve kid)
  allocate : ∀ packets, StateHistorySafe Good (hooks.allocate packets)
  create : ∀ pid item, StateHistorySafe Good (hooks.create pid item)
  front : ∀ family addr packets mtu, StateHistorySafe Good (hooks.front family addr packets mtu)
  poll : ProductHistorySafe Good hooks.poll
  encrypt : ∀ item, ProductHistorySafe Good (hooks.encrypt item)
  transmit : ∀ pid, ProductHistorySafe Good (hooks.transmit pid)

private def neutralConfirmation (hooks : Driver.Hooks E) : Driver.Hooks E :=
  {hooks with confirmation := fun pid kid => liftWGPrefix (receivedWithKeypair pid kid)}

private theorem quiet_hooks (h : QuietHooksSafe Good hooks) :
    HooksHistorySafe Good (neutralConfirmation hooks) where
  stagedPurge := h.stagedPurge
  peerRelease := h.peerRelease
  deliver := h.deliver
  keepalivePrepare := h.keepalivePrepare
  handshake := h.handshake
  fixtureEnter := h.fixtureEnter
  fixtureLeave := h.fixtureLeave
  sendWorker := h.sendWorker
  armTimer := h.armTimer
  queueSend := h.queueSend
  flushedSend := h.flushedSend
  candidateEnter := h.candidateEnter
  candidateLeave := h.candidateLeave
  stackInput := h.stackInput
  prepare := h.prepare
  counterCheck := h.counterCheck
  timerSelected := h.timerSelected
  timerFinished := h.timerFinished
  selection := h.selection
  confirmation := fun _ _ => Driver.History.state_lift _
  session := h.session
  reserve := h.reserve
  allocate := h.allocate
  create := h.create
  front := h.front
  poll := h.poll
  encrypt := h.encrypt
  transmit := h.transmit

theorem quiet_staging (h : QuietHooksSafe Good hooks) (pid : PeerId) :
    StateHistorySafe Good (Driver.stagingObserved hooks pid) :=
  Driver.staging_history (quiet_hooks h) pid

theorem quiet_keepalive (h : QuietHooksSafe Good hooks) (pid : PeerId) :
    StateHistorySafe Good (Driver.keepaliveObserved hooks pid) :=
  Driver.keepalive_actor_history (g := neutralConfirmation hooks) (quiet_hooks h).core pid

theorem quiet_receiveTail (h : QuietHooksSafe Good hooks) (pid : PeerId)
    (pkt : RxPacket) (confirmed : Bool) :
    StateHistorySafe Good (Driver.receiveTailObserved hooks pid pkt confirmed) :=
  Driver.receiveTail_history (quiet_hooks h) pid pkt confirmed

theorem quiet_stackFlush (h : QuietHooksSafe Good hooks) (packets : List (List UInt8)) :
    ProductHistorySafe Good (Driver.stackFlushObserved hooks packets) :=
  Driver.flush_history (quiet_hooks h) packets

theorem quiet_groReceive (cb : List (List UInt8) → PrefixM E Unit)
    (hc : ∀ ps, ProductHistorySafe Good (cb ps)) (gro : GroState) (pkt : List UInt8) :
    ProductHistorySafe Good (napiGroReceivePrefix cb gro pkt) :=
  (pinned_const _private.Leanux.Proofs.WG.TransmitSecurity.DriverHistoryReceive.«0».Leanux.Proofs.WG.TransmitSecurity.Driver.groReceive) cb hc gro pkt

theorem quiet_groFlush (cb : List (List UInt8) → PrefixM E Unit)
    (hc : ∀ ps, ProductHistorySafe Good (cb ps)) (gro : GroState) :
    ProductHistorySafe Good (napiGroFlushAllPrefix cb gro) :=
  (pinned_const _private.Leanux.Proofs.WG.TransmitSecurity.DriverHistoryReceive.«0».Leanux.Proofs.WG.TransmitSecurity.Driver.groFlush) cb hc gro

/-- The native poll preserves confirmation attribution while its other hooks
preserve history. Its confirmation contract is discharged at the true replay
guard on this source path, including retained prefixes before later Stop. -/
theorem quiet_nativePoll (record : AuthenticatedEffects.TransportDriver.Replay → E)
    (responder : ResponderEvent → E) (decode : E → Option ResponderEvent)
    (inverse : ∀ event, decode (responder event) = some event)
    (quiet : ∀ r, Unconfirmed decode (record r))
    (h : QuietHooksSafe (Safe record decode) hooks)
    (counter : hooks.counterCheck = AuthenticatedEffects.TransportDriver.counter record)
    (confirmed : hooks.confirmation = confirmation responder decode) (pid : PeerId) (budget : Nat) :
    ProductHistorySafe (Safe record decode) (Driver.nativePollObserved hooks pid budget) := by
  unfold Driver.nativePollObserved AuthenticatedEffects.GroOccurrencePoll.observed
  rw [counter]
  apply GroConfirmationOrder.poll record decode quiet hooks.candidateEnter hooks.candidateLeave
    _ _ _ h.candidateEnter h.candidateLeave
  · exact shared_consumer record responder decode inverse hooks confirmed
      (fun pid pkt value => (quiet_receiveTail h pid pkt value).liftWGObserver)
  · exact AuthenticatedEffects.GroOccurrence.receive_preserves (Base record decode) (Safe record decode)
      (fun _ _ hi => hi) _
      (AuthenticatedEffects.GroOccurrence.stack_preserves (Base record decode) (Safe record decode)
        (fun _ _ hi => hi) hooks.stackInput (Driver.stackObserved hooks)
        (fun bytes => by exact Driver.stack_history (g := neutralConfirmation hooks) (quiet_hooks h).core bytes) h.stackInput)
  · exact AuthenticatedEffects.GroOccurrence.flushAll_preserves (Base record decode) (Safe record decode)
      (fun _ _ hi => hi) _
      (AuthenticatedEffects.GroOccurrence.stack_preserves (Base record decode) (Safe record decode)
        (fun _ _ hi => hi) hooks.stackInput (Driver.stackObserved hooks)
        (fun bytes => by exact Driver.stack_history (g := neutralConfirmation hooks) (quiet_hooks h).core bytes) h.stackInput)

end Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder
