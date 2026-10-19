import Leanux.Proofs.WG.Roaming.HandshakeOverlayModel
import Leanux.Proofs.WG.Origins.HistoryAdapters
import Leanux.Proofs.WG.Lifetimes.ProductAmbient

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeOverlay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Origins
variable {E F α State : Type}

abbrev Event := Sum Origins.Event Attempt
def oldEvent : Event → Option Origins.Event
  | .inl e => some e
  | .inr _ => none
def attemptEvent : Event → Option Attempt
  | .inl _ => none
  | .inr r => some r
def old (a : PrefixM Origins.Event α) : PrefixM Event α :=
  focusPrefix Sum.inl oldEvent a

def Valid (h : List Event) : Prop :=
  ∀ r ∈ h.filterMap attemptEvent, Authenticated r

abbrev RxEvent := Sum Queues.RxHistory.Event Attempt
def rxEncode : Event → RxEvent
  | .inl e => .inl (HistoryAdapters.encode e)
  | .inr r => .inr r
def rxDecode : RxEvent → Option Event
  | .inl e => (HistoryAdapters.decode e).map Sum.inl
  | .inr r => some (.inr r)
def rxEvent : RxEvent → Option Queues.RxHistory.Event
  | .inl e => some e
  | .inr _ => none
def rxAttempt : RxEvent → Option Attempt
  | .inl _ => none
  | .inr r => some r
def RxValid (h : List RxEvent) : Prop :=
  ∀ r ∈ h.filterMap rxAttempt, Authenticated r


end Leanux.Proofs.WG.Roaming.HandshakeOverlay
