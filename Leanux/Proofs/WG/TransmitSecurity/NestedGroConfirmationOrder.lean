import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleasePollSource
import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceFrames
import Leanux.Proofs.WG.AuthenticatedEffects.CandidateScopeFrames
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationOrderPoll

/-! Confirmation attribution through the actual poll, including the peer
reference repayment after leaving each candidate scope. The repayment preserves
the supplied history invariant; authentication remains the consumer obligation. -/
namespace Leanux.Proofs.WG.TransmitSecurity.NestedGroConfirmationOrder
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
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
    (release : Option PeerId → PrefixM E Unit)
    (enter : SkbId → RxPacket → PrefixM E Nat) (leave : Nat → PrefixM E Unit)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (receive : GroOccurrence.Buffer → GroOccurrence.Entry → PrefixM E GroOccurrence.Buffer) (flush : GroOccurrence.Buffer → PrefixM E Unit)
    (releaseSafe : ∀ peer, PrefixPreserves (Base record decode) (Safe record decode) (release peer))
    (he : ∀ skb pkt, PrefixPreserves (Base record decode) (Safe record decode) (enter skb pkt))
    (hl : ∀ token, PrefixPreserves (Base record decode) (Safe record decode) (leave token))
    (hc : ∀ pid pkt ep, PrefixEnsures
      (fun h (_ : World) => Safe record decode h ∧ Accepted record pid pkt.keypair h)
      (Safe record decode) (consume pid pkt ep) (fun _ => Base record decode))
    (hr : ∀ gro bytes, PrefixPreserves (Base record decode) (Safe record decode) (receive gro bytes))
    (hf : ∀ gro, PrefixPreserves (Base record decode) (Safe record decode) (flush gro))
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves (Base record decode) (Safe record decode)
      (RetirementSecurity.NestedPeerRelease.pollWith (fun a => liftPrefix (liftWG a)) release enter leave (TransportDriver.counter record)
        consume receive flush pid budget) := by
  unfold RetirementSecurity.NestedPeerRelease.pollWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  change PrefixEnsures (Base record decode) (Safe record decode) _ (fun _ => Base record decode)
  repeat' first
    | order_contract
    | exact releaseSafe _
    | (replay_callback release; apply PrefixEnsures.bind (releaseSafe _))
    | (replay_callback release; apply leave_returned (releaseSafe _))
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

end Leanux.Proofs.WG.TransmitSecurity.NestedGroConfirmationOrder
