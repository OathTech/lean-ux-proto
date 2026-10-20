import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRxQueueFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLookupFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAccessCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedXmitConcreteComposition

/-! Fixed UDP ingress source syntax separates native RX allocation/free
from projection frames and exposes the actual counted peer repayments. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Ingress
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Driver NestedPeerRelease
abbrev History := List Event

inductive NativeKind : Type 1 where
  | quiet {α : Type} (body : WG.M α) (frame : SameView StagedEntry.view body)
      (allocated : Preserves StackOwnership.Allocated body)
  | access {α : Type} (body : WG.M α) (source : Access.Shape body)
      (allocated : Preserves StackOwnership.Allocated body)
  | lookup (kinds : List IndexKind) (number : Nat)
  | rxQueue (skb : SkbId)
  | allocate (packet : RxPacket)
  | free (skb : SkbId)

def NativeKind.Result : NativeKind → Type
  | @quiet α ..=>α
  | @access α ..=>α
  | .lookup _ _=>Option (IndexOwner × PeerId)
  | .rxQueue _=>Int
  | .allocate _=>SkbId
  | .free _=>Unit

def NativeKind.action (kind : NativeKind) : PrefixM Event kind.Result := match kind with
  | .quiet body ..=>liftWGObserver (liftWGPrefix body)
  | .access body ..=>liftWGObserver (liftWGPrefix body)
  | .lookup kinds number=>liftWGObserver (liftWGPrefix (indexLookup kinds number))
  | .rxQueue skb=>liftWGObserver (liftWGPrefix (enqueuePerDeviceAndPeerRx skb))
  | .allocate packet=>liftWGObserver (liftWGPrefix (newRxSkb packet))
  | .free skb=>liftWGObserver (liftWGPrefix (freeRxSkb skb))

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (kind : NativeKind) : Shape kind.action
  | release (peer : Option PeerId) : Shape (liftWGObserver (hooks.peerRelease peer))
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀value,Shape (next value)) : Shape (body >>= next)

noncomputable def pureShape (value : α) : Shape (liftWGObserver (pure value)) := by
  rw [liftWGObserver_pure]
  exact .pure value

noncomputable def observerBindShape {body : WGPrefix Event α} {next : α → WGPrefix Event β}
    (head : Shape (liftWGObserver body)) (tail : ∀value,Shape (liftWGObserver (next value))) :
    Shape (liftWGObserver (body >>= next)) := by
  rw [liftWGObserver_bind]
  exact .bind head tail

noncomputable def quietShape (body : WG.M α) (frame : SameView StagedEntry.view body)
    (allocated : Preserves StackOwnership.Allocated body) : Shape (liftWGObserver (liftWGPrefix body)) :=
  .native (.quiet body frame allocated)

noncomputable def accessShape (body : WG.M α) (source : Access.Shape body)
    (allocated : Preserves StackOwnership.Allocated body) : Shape (liftWGObserver (liftWGPrefix body)) :=
  .native (.access body source allocated)

noncomputable def conditionalShape (test : Prop) [Decidable test]
    {yes no : WGPrefix Event α} (left : test → Shape (liftWGObserver yes))
    (right : ¬test → Shape (liftWGObserver no)) : Shape (liftWGObserver (if test then yes else no)) := by
  split
  · exact left ‹_›
  · exact right ‹_›

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Ingress
