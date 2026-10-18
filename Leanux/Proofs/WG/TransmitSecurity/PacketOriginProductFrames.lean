import Leanux.Proofs.WG.TransmitSecurity.PacketOriginFrames

/-! Product-state frames for resident TX origins. Disposal and allocation
have separate contracts; these frames preserve the entire packet projection. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity

theorem product_store_inv (h : List Journal.Event) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : Inv h w.wg) : Inv h v.wg := by
  have device : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
  apply hi.retains
  apply Retains.of_snapshot
  change (epoch v.wg,PacketMaterial.view v.wg) = (epoch w.wg,PacketMaterial.view w.wg)
  apply Prod.ext
  · simp only [epoch,device]
  · funext id
    simp only [PacketMaterial.view,TxDisposition.txPackets,device]

theorem product_wire_inv {action : Leanux.M α} (same : SameView (fun w : World => txCryptWire w.wg) action) :
    Preserves (fun w : World => Inv h w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  have equal := (ProjectedAction.iff_run _ _ _).mp same w result v run
  apply before.retains
  apply Retains.of_snapshot
  change (epoch v.wg,PacketMaterial.view v.wg) = (epoch w.wg,PacketMaterial.view w.wg)
  apply Prod.ext
  · have ring := congrArg (fun s => s.1.map Prod.fst) equal
    simpa only [txCryptWire,TxRing.nativeCell,epoch,Option.map_map,Function.comp_def] using ring
  · funext id
    exact congrArg (fun s => (s.2 id).map PacketMaterial.material) equal

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
