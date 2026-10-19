import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollCallbackFrames

/-! The exact account follows the existing poll observer's phase and removal
journal. The selected front remains charged while only the remaining queued
carriers satisfy StableRx. Both bounds use the same durable holder witness. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Poll
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits
open DurableHolders RxJoint PollCarrier

def Context (front initial : RxCredits.Ledger) (loans : Reservations)
    (h : List RxJoint.Event) (w : World) : Prop :=
  ∃ holders, Phased holders (front ++ rest initial h) loans w.wg ∧ StableAt initial h w

abbrev Boundary := Context []

def Bare (initial : RxCredits.Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (h : List RxJoint.Event) (w : World) : Prop :=
  ∃ owner, owner.slot = pid ∧ stamp.2 = skb + 1 ∧ Context [Selected stamp owner] initial loans h w

def Live (initial : RxCredits.Ledger) (loans : Reservations) (pid skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) (h : List RxJoint.Event) (w : World) : Prop :=
  Bare initial loans pid skb stamp h w ∧ RxDisposition.SelectedAt skb stamp pkt w

theorem Context.lower (account : Context front initial loans h w) :
    DurableHolders.Accounted (fun ls h w => PollCarrier.Context front initial ls h w ∧ StableAt initial h w) loans h w := by
  obtain ⟨holders,account,stable⟩ := account
  exact ⟨holders,account.funded.aligned,account.funded.carriers,stable⟩

theorem Boundary.exact (account : Boundary initial loans h w) :
    ExactBoundary (rest initial h) loans w.wg := by
  obtain ⟨holders,account,stable⟩ := account
  exact ⟨holders,account.boundary stable⟩

theorem Boundary.start (account : ExactBoundary initial loans w.wg) (prior : List LifetimeEvent) :
    Boundary initial loans (seed prior) w := by
  obtain ⟨holders,account⟩ := account
  have empty : remaining initial [] = initial := List.filter_eq_self.mpr (fun _ _ => rfl)
  refine ⟨holders,?_,?_⟩ <;>
    simp only [StableAt,rest,seed_removedPackets,empty,List.nil_append]
  · exact account.phased
  · exact account.stable

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Poll
