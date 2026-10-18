import Leanux.Proofs.WG.Index.PollNapiCoreSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem rxPoll_index (pid : PeerId) (budget : Nat) :
    Campaign2.Product.Ensures (rxPoll pid budget (fun packets=>packets.forM Env.deliverInner))
      (fun s=>View.StagedIndexReady s.toSnapshot) (fun _ s=>View.StagedIndexReady s.toSnapshot) := by
  intro w result v pre run
  exact (StagingRich.ready_native v.wg v.ambient).mpr
    ((hoare_iff_run _ _ _).mp (PollCore.poll_ready pid budget) w result v
      ((StagingRich.ready_native w.wg w.ambient).mp pre) run)

theorem napiSoftirq_index :
    Campaign2.Product.Ensures Env.napiSoftirq
      (fun s=>View.StagedIndexReady s.toSnapshot) (fun _ s=>View.StagedIndexReady s.toSnapshot) := by
  intro w result v pre run
  exact (StagingRich.ready_native v.wg v.ambient).mpr
    ((hoare_iff_run _ _ _).mp PollCore.softirq_ready w result v
      ((StagingRich.ready_native w.wg w.ambient).mp pre) run)

theorem napiIrqExit_index :
    Campaign2.Product.Ensures Env.napiIrqExit
      (fun s=>View.StagedIndexReady s.toSnapshot) (fun _ s=>View.StagedIndexReady s.toSnapshot) := by
  intro w result v pre run
  exact (StagingRich.ready_native v.wg v.ambient).mpr
    ((hoare_iff_run _ _ _).mp PollCore.irqExit_ready w result v
      ((StagingRich.ready_native w.wg w.ambient).mp pre) run)

theorem pollScheduledInline_index :
    Campaign2.Product.Ensures Env.pollScheduledInline
      (fun s=>View.StagedIndexReady s.toSnapshot) (fun _ s=>View.StagedIndexReady s.toSnapshot) := by
  intro w result v pre run
  exact (StagingRich.ready_native v.wg v.ambient).mpr
    ((hoare_iff_run _ _ _).mp PollCore.inline_ready w result v
      ((StagingRich.ready_native w.wg w.ambient).mp pre) run)

end Leanux.Proofs.WG.Index
