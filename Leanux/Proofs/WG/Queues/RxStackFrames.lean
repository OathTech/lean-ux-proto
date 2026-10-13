import Leanux.Proofs.WG.Keypairs.Frames.EnvLeaves
import Leanux.Proofs.WG.Queues.RxCompletionFrame
import Leanux.Proofs.WG.Lifetimes.DeviceXmit
import Leanux.Proofs.Framing.Stack

/-! Concrete stack callbacks retain the exact receive queue, device epoch
and peer identity of every surviving resident. Transmit error and cleanup
paths may delete residents; no ownership or packet-validity premise is used. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem loopbackSoftirq_kernel : SameKernel loopbackSoftirq := by
  rw [loopbackSoftirq_source]
  apply sameKernel_of_wp
  intro k
  have hf := sameKernel_wp _ loopbackFinish_sameKernel (fun s => s = k)
  mvcgen [getDev, getK, hf, unsupported, invariant]

theorem loopbackSend_kernel (sites : List HiddenSite) (raised : Bool) :
    SameKernel (loopbackSend sites raised) := by
  apply sameKernel_of_wp
  intro k
  have hs := sameKernel_wp _ (skipCut_sameKernel sites) (fun s => s = k)
  have hr := sameKernel_wp _ raiseLoopbackRx_sameKernel (fun s => s = k)
  have hl := sameKernel_wp _ loopbackSoftirq_kernel (fun s => s = k)
  mvcgen [loopbackSend, hs, hr, hl]

theorem lookupDst_rxQueues (family addr : Nat) :
    SameView rxQueues (lookupDst family addr) := by
  apply SameView.of_wp
  intro s
  have hl := fun root bits key => (lookup_rxQueues root bits key).wp (fun t => t = s)
  mvcgen [lookupDst, hl, getDev, getK, branch, invariant]

theorem xmitTrim_rxQueues (pid : PeerId) : SameView rxQueues (xmitTrim pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_rx_spec (fun t => t = s) pid
  have hs := fun p => setPeer_rx_spec (fun t => t = s) pid p
  have hd := (modifyDev_rxQueues (fun d => {d with txDropped := d.txDropped + 1})
    (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec rxQueues (α := α) (β := β) (fun t => t = s)
  simp only [xmitTrim, Std.Legacy.Range.forIn_eq_forIn_range']
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, hg, hs, hd, branch]
  all_goals try exact ((⇓? _ w => ⌜rxQueues w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all [CurrentRx]

theorem xmitSplice_rxQueues (pid : PeerId) (packets : List Packet) :
    SameView rxQueues (xmitSplice pid packets) := by
  simp only [xmitSplice, getPeer_twice]
  exact modifyPeer_rxQueues pid (fun p => {p with staged := p.staged ++ packets})
    (fun _ => rfl) (fun _ => rfl)

/-- Original transmit entry retains surviving receive queues on every normal
return, including negative status codes. Its full source factor keeps both
getters in the splice and all protocol, allocation and loopback error paths. -/
theorem wgXmit_rxQueues (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    RetainsRx (wgXmit family addr packets mtu) := by
  rw [wgXmitSource_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have hg := fun pid => (getPeer_rxQueues pid).wp P
  have hlookup := (lookupDst_rxQueues family addr).wp P
  have htrim := fun pid => (xmitTrim_rxQueues pid).wp P
  have hsplice := fun pid packets => (xmitSplice_rxQueues pid packets).wp P
  have hstage := fun pid => (sendStagedPackets_rxQueues pid).wp s
  have hput := fun pid => (peerPut_rxQueues pid).wp s
  have hloop := fun sites raised => (rxQueues_kernel (loopbackSend_kernel sites raised)).wp P
  have hcut := fun sites => (rxQueues_kernel (skipCutSites_sameKernel sites)).wp P
  have henv := fun site => (rxQueues_kernel (envOk_sameKernel site)).wp P
  have herr := (modifyDev_rxQueues (fun d => {d with txErrors := d.txErrors + 1})
    (fun _ => rfl) (fun _ => rfl)).wp P
  have hl (α β : Type) := list_view_spec rxQueues (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, wgXmitSource,
    hg, hlookup, htrim, hsplice, hstage, hput, hloop, hcut, henv, herr,
    WG.andM, branch, invariant, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact rx_retained_refl _ | trivial

theorem reply4_rxQueues (dst : Nat) (bytes : List UInt8) :
    RetainsRx (Leanux.Env.Stack.reply4 dst bytes) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have hc := fun sites => (rxQueues_kernel (skipCut_sameKernel sites)).wp P
  have hx := fun family addr packets mtu => (wgXmit_rxQueues family addr packets mtu).wp s
  have hd (α : Type) := discard_view_spec rxQueues (α := α) P
  mvcgen [Leanux.Env.Stack.reply4, hc, hx, hd, getDev, getK, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst s
  all_goals exact rx_retained_refl _

theorem receive4_rxQueues (bytes : List UInt8) :
    RetainsRx (Leanux.Env.Stack.receive4 bytes) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have hr := fun dst bytes => (reply4_rxQueues dst bytes).wp s
  mvcgen [Leanux.Env.Stack.receive4, Leanux.Env.Stack.excluded, hr, getK, invariant, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst s
  all_goals exact rx_retained_refl _

theorem deliverInner_rxQueues (bytes : List UInt8) : RetainsRx (Leanux.Env.deliverInner bytes) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have h4 := (receive4_rxQueues bytes).wp s
  have h6 := (rxQueues_kernel (stackReceive6_sameKernel bytes)).wp P
  mvcgen [Leanux.Env.deliverInner, Leanux.Env.Stack.receive, h4, h6, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals subst s
  all_goals exact rx_retained_refl _

theorem stackForM_rxQueues (packets : List (List UInt8)) :
    RetainsRx (packets.forM Leanux.Env.deliverInner) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have hi : ∀ packets : List (List UInt8),
      ⦃fun w => ⌜P (rxQueues w)⌝⦄ packets.forM Leanux.Env.deliverInner
        ⦃⇓? _ w => ⌜P (rxQueues w)⌝⦄ := by
    intro xs
    induction xs with
    | nil => mvcgen
    | cons bytes xs ih =>
      have hb := (deliverInner_rxQueues bytes).wp s
      simp only [List.forM_eq_forM, List.forM_cons] at *
      mvcgen [hb, ih]
  mvcgen [hi]
  subst s
  exact rx_retained_refl _

end Leanux.Proofs.WG.Queues
