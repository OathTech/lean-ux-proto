import Leanux.Proofs.WG.AuthenticatedEffects.CandidateScopeFrames
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationOrderPoll

/-! Candidate scope markers are outside the current replay-to-confirmation
interval. This independently transports exact confirmation order through the
scoped poll; actual packet authentication remains the other same-journal fact. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CandidateOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open HandshakeSecurity.ConfirmationTransportOrder
open Lifetimes Queues RxJoint
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
variable {E : Type} {recordReplay : TransportDriver.Replay → E}
  {decode : E → Option HandshakeSecurity.Responder.DriverCuts.Event}

private theorem leave_returned {g : PrefixM E α} {f : α → PrefixM E β}
    (hg : PrefixPreserves (Base recordReplay decode) (Safe recordReplay decode) g)
    (hf : ∀ x, PrefixEnsures (Base recordReplay decode) (Safe recordReplay decode) (f x) Q) :
    PrefixEnsures (Returned recordReplay decode pkt value) (Safe recordReplay decode) (g >>= f) Q :=
  (PrefixEnsures.bind hg hf).consequence (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)

theorem poll
    (record : TransportDriver.Replay → E) (decode : E → Option HandshakeSecurity.Responder.DriverCuts.Event)
    (quiet : ∀ r, Unconfirmed decode (record r))
    (enter : SkbId → RxPacket → PrefixM E Nat) (leave : Nat → PrefixM E Unit)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (receive : GroState → List UInt8 → PrefixM E GroState) (flush : GroState → PrefixM E Unit)
    (he : ∀ skb pkt, PrefixPreserves (Base record decode) (Safe record decode) (enter skb pkt))
    (hl : ∀ token, PrefixPreserves (Base record decode) (Safe record decode) (leave token))
    (hc : ∀ pid pkt ep, PrefixEnsures
      (fun h (_ : World) => Safe record decode h ∧ Accepted record pid pkt.keypair h)
      (Safe record decode) (consume pid pkt ep) (fun _ => Base record decode))
    (hr : ∀ gro bytes, PrefixPreserves (Base record decode) (Safe record decode) (receive gro bytes))
    (hf : ∀ gro, PrefixPreserves (Base record decode) (Safe record decode) (flush gro))
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves (Base record decode) (Safe record decode)
      (CandidatePoll.sourceWith (fun a => liftPrefix (liftWG a)) enter leave (TransportDriver.counter record)
        consume receive flush pid budget) := by
  unfold CandidatePoll.sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  change PrefixEnsures (Base record decode) (Safe record decode) _ (fun _ => Base record decode)
  repeat' first
    | order_contract
    | exact he _ _
    | exact hl _
    | (replay_callback enter; apply PrefixEnsures.bind (he _ _))
    | (replay_callback leave; apply PrefixEnsures.bind (hl _))
    | (replay_callback leave; apply leave_returned (hl _))
    | (replay_callback consume; apply (pinned_const _private.Leanux.Proofs.WG.HandshakeSecurity.ConfirmationOrderPoll.«0».Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder.consume_bind) consume hc
       · simp_all
       · simp_all)
    | (replay_callback receive; exact hr _ _)
    | (replay_callback flush; exact hf _)
    | (rx_phase_head plain TransportDriver.counter; apply PrefixEnsures.bind ((pinned_const _private.Leanux.Proofs.WG.HandshakeSecurity.ConfirmationOrderPoll.«0».Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder.counter) record decode quiet _ _))
    | (replay_native_head invariant; apply (pinned_const _private.Leanux.Proofs.WG.HandshakeSecurity.ConfirmationOrderPoll.«0».Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder.stopped); intro h w hi; first | exact hi | exact hi.1)
    | (replay_native_head keypairPut; apply (pinned_const _private.Leanux.Proofs.WG.HandshakeSecurity.ConfirmationOrderPoll.«0».Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder.cleanup))
    | (replay_native_head branch; apply (pinned_const _private.Leanux.Proofs.WG.HandshakeSecurity.ConfirmationOrderPoll.«0».Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder.branch_bind)
       · intro h hi; first | exact hi | exact hi.1
       intro result equal)
    | (replay_head liftPrefix; apply (pinned_const _private.Leanux.Proofs.WG.HandshakeSecurity.ConfirmationOrderPoll.«0».Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder.native); intro h hi; first | exact hi | exact hi.1)
    | (replay_head Bind.bind; apply (pinned_const _private.Leanux.Proofs.WG.HandshakeSecurity.ConfirmationOrderPoll.«0».Leanux.Proofs.WG.HandshakeSecurity.ConfirmationTransportOrder.flow_bind))
    | (replay_head ForIn.forIn; apply PrefixPreserves.forIn)
    | (replay_head Pure.pure; apply PrefixEnsures.pure
       · intro h w hi; first | exact hi | exact hi.1
       · intro h w hi; first | exact hi | exact hi.1)
    | (replay_head ite; apply PrefixEnsures.ite)
    | rx_phase_reduce
    | rx_phase_match
    | (rx_phase_intro; try dsimp only)
    | assumption
    | exact fun (h : List E) (w : World) (hi : Base record decode h w) => hi

/-- The shared native consumer still receives the exact current replay occurrence
when candidate markers bracket the entire counter and consumer interval. -/
theorem shared_poll (record : TransportDriver.Replay → E)
    (responder : HandshakeSecurity.Responder.DriverCuts.Event → E)
    (decode : E → Option HandshakeSecurity.Responder.DriverCuts.Event)
    (inverse : ∀ event, decode (responder event) = some event)
    (quiet : ∀ r, Unconfirmed decode (record r))
    (hooks : TransmitSecurity.Driver.Hooks E)
    (enter : SkbId → RxPacket → PrefixM E Nat) (leave : Nat → PrefixM E Unit)
    (he : ∀ skb pkt, PrefixPreserves (Base record decode) (Safe record decode) (enter skb pkt))
    (hl : ∀ token, PrefixPreserves (Base record decode) (Safe record decode) (leave token))
    (confirmed : hooks.confirmation = confirmation responder decode)
    (tail : ∀ pid pkt value, PrefixPreserves (Base record decode) (Safe record decode)
      (liftWGObserver (TransmitSecurity.Driver.receiveTailObserved hooks pid pkt value)))
    (toStack : List (List UInt8) → PrefixM E Unit)
    (receive : ∀ gro bytes, PrefixPreserves (Base record decode) (Safe record decode)
      (napiGroReceivePrefix toStack gro bytes))
    (flush : ∀ gro, PrefixPreserves (Base record decode) (Safe record decode)
      (napiGroFlushAllPrefix toStack gro)) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (Base record decode) (Safe record decode)
      (CandidatePoll.sourceWith (fun a => liftPrefix (liftWG a)) enter leave
        (TransportDriver.counter record)
        (fun pid pkt ep => liftWGObserver (TransmitSecurity.Driver.consumeObserved hooks pid pkt ep))
        (napiGroReceivePrefix toStack) (napiGroFlushAllPrefix toStack) pid budget) :=
  poll record decode quiet enter leave _ _ _ he hl
    (shared_consumer record responder decode inverse hooks confirmed tail) receive flush pid budget

end Leanux.Proofs.WG.AuthenticatedEffects.CandidateOrder
