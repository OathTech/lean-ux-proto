import Leanux.Proofs.WG.Index.TransmitCoreSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem wgXmit_index (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Campaign2.Ensures (wgXmit family addr packets mtu) View.StagedIndexReady
      (fun _=>View.StagedIndexReady) := by
  intro w a result v b pre run
  exact (StagingRich.ready_native v b).mpr
    ((hoare_iff_run_ambient _ _ _).mp (TransmitCore.wgXmit_ready family addr packets mtu)
      w a result v b ((StagingRich.ready_native w a).mp pre) run)

theorem deliverInner_index (bytes : List UInt8) :
    Campaign2.Product.Ensures (Env.deliverInner bytes)
      (fun s=>View.StagedIndexReady s.toSnapshot)
      (fun _ s=>View.StagedIndexReady s.toSnapshot) := by
  intro w result v pre run
  exact (StagingRich.ready_native v.wg v.ambient).mpr
    ((hoare_iff_run _ _ _).mp (TransmitCore.stack_ready bytes) w result v
      ((StagingRich.ready_native w.wg w.ambient).mp pre) run)

end Leanux.Proofs.WG.Index
