import Leanux.Proofs.WG.Lifetimes.TxCallSource

/-! Exact product-focus distribution through the actual transmit syscall body.
The original callbacks must append to their actual incoming histories. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Configuration

private def ProductFocused {E F α : Type} (encode : E → F) (decode : F → Option E)
    (g : PrefixM F α) (a : PrefixM E α) : Prop :=
  Appends a ∧ g = focusPrefix encode decode a

private theorem productFocused_pure {E F α : Type} (encode : E → F) (decode : F → Option E)
    (x : α) : ProductFocused encode decode (pure x) (pure x) := by
  refine ⟨Appends.pure x, ?_⟩
  funext w h
  exact FocusesUnder.pure (I := fun _ _ => True) x w h True.intro

private theorem productFocused_lift {E F α : Type} (encode : E → F) (decode : F → Option E)
    (a : Leanux.M α) : ProductFocused encode decode (liftPrefix a) (liftPrefix a) := by
  refine ⟨Appends.lift a, ?_⟩
  funext w h
  exact FocusesUnder.lift (I := fun _ _ => True) a w h True.intro

private theorem productFocused_bind {E F α β : Type} (encode : E → F) (decode : F → Option E)
    (inverse : ∀ e, decode (encode e) = some e)
    {g : PrefixM F α} {a : PrefixM E α}
    {f : α → PrefixM F β} {b : α → PrefixM E β}
    (hg : ProductFocused encode decode g a)
    (hf : ∀ x, ProductFocused encode decode (f x) (b x)) :
    ProductFocused encode decode (g >>= f) (a >>= b) := by
  refine ⟨hg.1.bind (fun x => (hf x).1),?_⟩
  rw [hg.2,show f = (fun x => focusPrefix encode decode (b x)) from funext (fun x => (hf x).2)]
  funext w h
  exact focusPrefix_bind_appends encode decode inverse hg.1 (fun x => (hf x).1) w h

/-- Focused callbacks recover the whole old syscall on exactly its projected
incoming history. No history-independence premise is used. -/
theorem syscallXmitWith_focus {E F : Type} (encode : E → F) (decode : F → Option E)
    (inverse : ∀ e, decode (encode e) = some e)
    (multicast : Nat → Nat → PrefixM E Unit)
    (xmit : Nat → Nat → List Packet → Nat → PrefixM E Int)
    (hm : ∀ family addr, Appends (multicast family addr))
    (hx : ∀ family addr packets mtu, Appends (xmit family addr packets mtu))
    (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    syscallXmitWith (fun family addr => focusPrefix encode decode (multicast family addr))
      (fun family addr packets mtu => focusPrefix encode decode (xmit family addr packets mtu))
      family addr payload opts =
    focusPrefix encode decode (syscallXmitWith multicast xmit family addr payload opts) := by
  suffices goal : ProductFocused encode decode
      (syscallXmitWith (fun family addr => focusPrefix encode decode (multicast family addr))
        (fun family addr packets mtu => focusPrefix encode decode (xmit family addr packets mtu))
        family addr payload opts)
      (syscallXmitWith multicast xmit family addr payload opts) from goal.2
  unfold syscallXmitWith socketCallOnWith
  repeat' first
    | exact ⟨hm _ _,rfl⟩
    | exact ⟨hx _ _ _ _,rfl⟩
    | exact productFocused_lift encode decode _
    | exact productFocused_pure encode decode _
    | apply productFocused_bind encode decode inverse
    | maintenance_intro
    | dsimp only
    | split

/-- The original multicast arm either focuses its actual loopback journal or
runs a raw stopping/pure action; all outcomes retain the incoming history. -/
theorem xmitMulticastLoopAudit_appends (family addr : Nat) :
    Appends (xmitMulticastLoopAudit family addr) := by
  unfold xmitMulticastLoopAudit
  split
  · exact Appends.focus _ _ _
  · split
    · exact Appends.lift _
    · exact Appends.pure _

end Leanux.Proofs.WG.Lifetimes
