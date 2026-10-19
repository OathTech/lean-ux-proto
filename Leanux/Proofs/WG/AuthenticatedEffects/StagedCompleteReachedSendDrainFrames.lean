import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendDrainSource

/-! Native send-drain bookkeeping and both concrete callbacks preserve the
same complete packet account and allocation companion on successful prefixes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity CausalJournal
open CompleteProduct

theorem front_checked : Checked front := by
  unfold front
  apply bind_checked wg_read
  intro w
  split
  · exact pure_checked _
  · exact bind_checked (product_store _ requireNoCryptWork_sameKernel) (fun _ =>
      bind_checked (wg_bookkeeping _ (fun _ => rfl)) (fun _ =>
        bind_checked (ambient _) (fun _ => pure_checked _)))

theorem schedule_checked : Checked (Driver.scheduleObserved hooks none) :=
  schedule encrypt_iteration decrypt_iteration receive_iteration
    (fun pid => tx_iter pid (tx_worker pid)) softirq none

theorem read_checked : Checked (liftPrefix (liftWG getDev)) :=
  wg _ (state_store _ getDev_sameWGStore)

theorem step_checked (index : Nat) (acc : LoopState) : Checked (step index acc) := by
  unfold step
  apply bind_checked read_checked
  intro d
  split
  · exact bind_checked delivery (fun _ => pure_checked _)
  · exact bind_checked scheduled_send (fun _ => bind_checked schedule_checked (fun _ => pure_checked _))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendDrain
