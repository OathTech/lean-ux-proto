import Leanux.Proofs.WG.TransmitSecurity.NonceSessionFrames
import Leanux.Proofs.WG.Packets.TxFront

/-! The actual transmit front cannot change a sending nonce frontier. These
frames stop before staging, where the native reservation observer takes over. -/
set_option maxHeartbeats 600000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Packets Queues

theorem store {α : Type} {a : WG.M α} (frame : SameWGStore a) : SameView view a :=
  frame.of_factor
    (fun s => View.mk s.keypairCounter
      (fun id => (s.dev.bind fun d => d.keypairs[id]?).map Nonce.cell))
    view (fun _ => rfl)

theorem lookup (family addr : Nat) : SameView view (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl hr
  cases result with
  | none =>
    change wgStoreView v = wgStoreView w at borrowed
    exact congrArg (fun s => View.mk s.keypairCounter
      (fun id => (s.dev.bind fun d => d.keypairs[id]?).map Nonce.cell)) borrowed
  | some pid =>
    obtain ⟨d,p,hd,hp,_,hv⟩ := borrowed
    have dev := congrArg WGStoreView.dev hv
    have frontier := congrArg WGStoreView.keypairCounter hv
    apply View.ext
    · exact frontier
    · funext id
      change v.dev = some _ at dev
      change w.dev = some d at hd
      simp only [view,dev,hd,Option.bind_some]

theorem trim (pid : PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (xmitTrim pid) := by
  unfold xmitTrim
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
  repeat' nonce_preserves_step h

theorem splice (pid : PeerId) (packets : List Packet) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (xmitSplice pid packets) := by
  unfold xmitSplice
  repeat' nonce_preserves_step h

theorem tx_front (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (txFront family addr packets mtu) := by
  unfold txFront txCheck txSelect txError txHeaders txWalk WG.andM
  simp (config := {zeta := false}) only [branch,invariant,skipCutSites,envOk]
  repeat' first
    | (rx_retention_head lookupDst; exact native_frame h (lookup _ _))
    | (rx_retention_head xmitTrim; exact trim _ h)
    | (rx_retention_head xmitSplice; exact splice _ _ h)
    | (rx_retention_head loopbackSend; exact native_frame h (store (loopbackSend_kernel _ _)))
    | (allocation_release_lift_from Net.M; exact native_frame h (store (liftRouting_sameWGStore _)))
    | nonce_preserves_step h

end Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
