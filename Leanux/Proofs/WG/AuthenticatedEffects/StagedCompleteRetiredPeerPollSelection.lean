import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollNativeFrames

/-! Actual poll selection facts, kept beside the same exact account. The
ready condition comes from the original readiness observer. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Poll
open Leanux Leanux.WG Lifetimes Queues Queues.RxCredits

def AfterPeek (initial : RxCredits.Ledger) (loans : Reservations) (pid : PeerId)
    (first : Option SkbId) (h : List RxJoint.Event) (w : World) : Prop :=
  Boundary initial loans h w ∧ Peeked pid first w.wg ∧ HeadAt pid first w

def Checked (initial : RxCredits.Ledger) (loans : Reservations) (pid : PeerId)
    (first : Option SkbId) (go : Bool) (h : List RxJoint.Event) (w : World) : Prop :=
  Boundary initial loans h w ∧ Peeked pid first w.wg ∧
    (go = false → ColdHead pid w.wg) ∧ (go = true → ReadyPacket first w)

def Captured (initial : RxCredits.Ledger) (loans : Reservations) (pid skb : Nat)
    (out : RxPacket × PacketStamp) (h : List RxJoint.Event) (w : World) : Prop :=
  Boundary initial loans h w ∧ Peeked pid (some skb) w.wg ∧
    RxDisposition.SelectedAt skb out.2 out.1 w ∧ out.1.state ≠ .uncrypted

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Poll
