import Leanux.Proofs.WG.AuthenticatedEffects.CandidateOrder

/-! Concrete lexical markers cannot manufacture responder confirmations. The
same actual candidate poll keeps its independent confirmation-order contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CandidateOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open HandshakeSecurity.ConfirmationTransportOrder
open Lifetimes Queues RxJoint
variable {E Cause : Type}

theorem scope_enter (record : TransportDriver.Replay → E)
    (decode : E → Option HandshakeSecurity.Responder.DriverCuts.Event)
    (scopeRecord : CausalScope.Event Cause → E)
    (quiet : ∀ event, Unconfirmed decode (scopeRecord event)) (cause : Cause) :
    PrefixPreserves (Base record decode) (Safe record decode)
      (CausalScope.enterPrefix scopeRecord cause) := by
  intro w h hi
  let event := scopeRecord (.entered ⟨h.length,cause⟩)
  have kept : Safe record decode (h ++ [event]) := hi.quiet (by
    intro e member
    obtain rfl := List.mem_singleton.mp member
    exact quiet _)
  exact ⟨[event],rfl,kept,kept⟩

theorem scope_leave (record : TransportDriver.Replay → E)
    (decode : E → Option HandshakeSecurity.Responder.DriverCuts.Event)
    (scopeRecord : CausalScope.Event Cause → E)
    (quiet : ∀ event, Unconfirmed decode (scopeRecord event)) (position : Nat) :
    PrefixPreserves (Base record decode) (Safe record decode)
      (CausalScope.leavePrefix scopeRecord position) := by
  intro w h hi
  let event := scopeRecord (.exited position)
  have kept : Safe record decode (h ++ [event]) := hi.quiet (by
    intro e member
    obtain rfl := List.mem_singleton.mp member
    exact quiet _)
  exact ⟨[event],rfl,kept,kept⟩

theorem scoped_shared_poll (record : TransportDriver.Replay → E)
    (responder : HandshakeSecurity.Responder.DriverCuts.Event → E)
    (decode : E → Option HandshakeSecurity.Responder.DriverCuts.Event)
    (inverse : ∀ event, decode (responder event) = some event)
    (quiet : ∀ r, Unconfirmed decode (record r))
    (scopeRecord : CausalScope.Event Cause → E) (candidate : SkbId → RxPacket → Cause)
    (scopeQuiet : ∀ event, Unconfirmed decode (scopeRecord event))
    (hooks : TransmitSecurity.Driver.Hooks E)
    (confirmed : hooks.confirmation = confirmation responder decode)
    (tail : ∀ pid pkt value, PrefixPreserves (Base record decode) (Safe record decode)
      (liftWGObserver (TransmitSecurity.Driver.receiveTailObserved hooks pid pkt value)))
    (toStack : List (List UInt8) → PrefixM E Unit)
    (receive : ∀ gro bytes, PrefixPreserves (Base record decode) (Safe record decode)
      (napiGroReceivePrefix toStack gro bytes))
    (flush : ∀ gro, PrefixPreserves (Base record decode) (Safe record decode)
      (napiGroFlushAllPrefix toStack gro)) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (Base record decode) (Safe record decode)
      (CandidatePoll.sourceWith (fun a => liftPrefix (liftWG a))
        (fun skb pkt => CausalScope.enterPrefix scopeRecord (candidate skb pkt))
        (CausalScope.leavePrefix scopeRecord) (TransportDriver.counter record)
        (fun pid pkt ep => liftWGObserver (TransmitSecurity.Driver.consumeObserved hooks pid pkt ep))
        (napiGroReceivePrefix toStack) (napiGroFlushAllPrefix toStack) pid budget) :=
  shared_poll record responder decode inverse quiet hooks _ _
    (fun skb pkt => scope_enter record decode scopeRecord scopeQuiet (candidate skb pkt))
    (fun token => scope_leave record decode scopeRecord scopeQuiet token)
    confirmed tail toStack receive flush pid budget

end Leanux.Proofs.WG.AuthenticatedEffects.CandidateOrder
