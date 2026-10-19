import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxHistoryFrames
import Leanux.Proofs.WG.Queues.HolderEntryDispatch

/-! Routed transmit absorbs the actual native handoff delta. The external
socket/route/packetization wrapper retains that same RX reference account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem Account.transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat)
    (account : Account holders carriers loans w)
    (run : ((wgXmit family addr packets mtu).run w).run a=.ok ((result,v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧ Account (holders.absorb delta) carriers loans v := by
  obtain ⟨delta,step,funded,stable⟩ := HolderXmit.funded family addr packets mtu
    account.funded account.stable a b run
  have upper : Upper holders carriers (loans ++ []) w := by simpa using account.upper
  exact ⟨delta,step,funded,by simpa using upper.handoff step,stable⟩

theorem ExactBoundary.transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (ExactBoundary carriers loans) (wgXmit family addr packets mtu) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  rintro w a result v b ⟨holders,account⟩ run
  obtain ⟨delta,_,after⟩ := account.transmit family addr packets mtu run
  exact ⟨holders.absorb delta,after⟩

theorem ExactAt.transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True)
      (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) :=
  ExactAt.mixed _ _ (liftWGObserver_erases (wgXmitPrefix_erases family addr packets mtu))
    (fun _ => ExactBoundary.lift _ (ExactBoundary.transmit family addr packets mtu))

namespace Transmit

private theorem ambient (action : AmbientM α) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ hi => hi)

private theorem fs (action : FS.M α) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (liftFS action) :=
  productFS_spec action _ (fun _ _ _ _ hi => hi)

private theorem routing (action : Net.M α) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (monadLift action : Leanux.M α) :=
  ExactBoundary.product_frame _ (fun initial => productRouting_spec action (fun s => s=initial))

theorem dispatch (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Preserves (fun w : World => ExactBoundary cs loans w.wg) (Leanux.dispatch (.wgXmit family addr payload opts)) := by
  unfold Leanux.dispatch socketCallOn
  simp (config := {zeta := false}) only [unsupported,Env.fixtureSend,skipCut]
  repeat' first
    | (allocation_release_lift_from WG.M; exact ExactBoundary.lift _ (ExactBoundary.transmit _ _ _ _))
    | (rx_retention_head Env.xmitMulticastLoop; exact ExactBoundary.product_frame _
        ((pinned_const _private.Leanux.Proofs.WG.Queues.BatchAccount.«0».Leanux.Proofs.WG.Queues.RxCredits.BatchAccount.multicast_store) _ _))
    | (rx_retention_head Env.xmitPackets; exact ExactBoundary.product_frame _ (xmitPackets_sameKernel _ _ _ _))
    | (rx_retention_head getWG; exact ExactBoundary.product_frame _ (fun initial => productGetWG_spec (fun s => s=initial)))
    | (allocation_release_lift_from Net.M; exact routing _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_lift_from FS.M; exact fs _)
    | rx_retention_step

end Transmit
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
