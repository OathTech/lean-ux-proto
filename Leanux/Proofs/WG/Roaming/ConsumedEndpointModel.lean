import Leanux.Proofs.WG.Noise.ConfirmationOrderClaims
import Leanux.Proofs.WG.Roaming.View

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.ConsumedEndpoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Queues Lifetimes RxJoint
variable {α β : Type}

def Facts (r : RxDisposition.ConsumeReceipt) : Prop :=
  r.endpoint = sourceEndpoint r.packet.source ∧
  (r.packet.source.family = 4 ∨ r.packet.source.family = 6)

def EventFacts : RxJoint.Event → Prop
  | .consumed _ _ _ r => Facts r
  | _ => True

def Checks (h : List RxJoint.Event) : Prop := ∀ e ∈ h, EventFacts e

theorem checks_append {h t : List RxJoint.Event} (a : Checks h) (b : Checks t) :
    Checks (h ++ t) := by
  intro e member
  exact (List.mem_append.mp member).elim (a e) (b e)

theorem checks_snoc {h : List RxJoint.Event} (hi : Checks h) (e : RxJoint.Event)
    (he : EventFacts e) : Checks (h ++ [e]) :=
  checks_append hi (by intro x hx; simpa only [List.mem_singleton.mp hx] using he)


end Leanux.Proofs.WG.Roaming.ConsumedEndpoint
