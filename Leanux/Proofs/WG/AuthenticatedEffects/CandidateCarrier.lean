import Leanux.Proofs.WG.AuthenticatedEffects.CandidateOrderScope
import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierBase

/-! The carrier and confirmation-order properties concern one exact scoped
native receive action. Lexical entry does not authorize the candidate packet. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CandidateCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged
open HandshakeSecurity.ConfirmationTransportOrder
open Lifetimes Queues RxJoint
variable {E Cause : Type}

theorem scoped_shared_poll
    (origin : E → Option TransportDriver.OriginEvent) (replay : E → Option TransportDriver.Replay)
    (record : TransportDriver.Replay → E)
    (replayInverse : ∀ r, replay (record r) = some r) (replayOrigin : ∀ r, origin (record r) = none)
    (responder : HandshakeSecurity.Responder.DriverCuts.Event → E)
    (decode : E → Option HandshakeSecurity.Responder.DriverCuts.Event)
    (inverse : ∀ event, decode (responder event) = some event)
    (quiet : ∀ r, Unconfirmed decode (record r))
    (scopeRecord : CausalScope.Event Cause → E) (candidate : SkbId → RxPacket → Cause)
    (scopeOrigin : ∀ event, origin (scopeRecord event) = none)
    (scopeReplay : ∀ event, replay (scopeRecord event) = none)
    (scopeQuiet : ∀ event, Unconfirmed decode (scopeRecord event))
    (hooks : TransmitSecurity.Driver.Hooks E)
    (confirmed : hooks.confirmation = confirmation responder decode)
    (toStack : List (List UInt8) → PrefixM E Unit)
    (consumeCarrier : ∀ pid pkt ep, TransportReplay.Preserves (origin := origin) (replay := replay)
      (liftWGObserver (TransmitSecurity.Driver.consumeObserved hooks pid pkt ep)))
    (receiveCarrier : ∀ gro bytes, TransportReplay.Preserves (origin := origin) (replay := replay)
      (napiGroReceivePrefix toStack gro bytes))
    (flushCarrier : ∀ gro, TransportReplay.Preserves (origin := origin) (replay := replay)
      (napiGroFlushAllPrefix toStack gro))
    (tailOrder : ∀ pid pkt value, PrefixPreserves (Base record decode) (Safe record decode)
      (liftWGObserver (TransmitSecurity.Driver.receiveTailObserved hooks pid pkt value)))
    (receiveOrder : ∀ gro bytes, PrefixPreserves (Base record decode) (Safe record decode)
      (napiGroReceivePrefix toStack gro bytes))
    (flushOrder : ∀ gro, PrefixPreserves (Base record decode) (Safe record decode)
      (napiGroFlushAllPrefix toStack gro)) (pid : PeerId) (budget : Nat) :
    TransportCarrier.ProductSafe (Safe record decode) origin replay
      (CandidatePoll.sourceWith (fun a => liftPrefix (liftWG a))
        (fun skb pkt => CausalScope.enterPrefix scopeRecord (candidate skb pkt))
        (CausalScope.leavePrefix scopeRecord) (TransportDriver.counter record)
        (fun pid pkt ep => liftWGObserver (TransmitSecurity.Driver.consumeObserved hooks pid pkt ep))
        (napiGroReceivePrefix toStack) (napiGroFlushAllPrefix toStack) pid budget) :=
  TransportCarrier.product_combine _
    (TransportReplay.scoped_poll_checked origin replay record replayInverse replayOrigin
      scopeRecord candidate scopeOrigin scopeReplay _ _ _ consumeCarrier receiveCarrier flushCarrier pid budget)
    (CandidateOrder.scoped_shared_poll record responder decode inverse quiet
      scopeRecord candidate scopeQuiet hooks confirmed tailOrder toStack receiveOrder flushOrder pid budget)

end Leanux.Proofs.WG.AuthenticatedEffects.CandidateCarrier
