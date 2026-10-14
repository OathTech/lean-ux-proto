import Leanux.Proofs.WG.Queues.RxNapiCuts
import Leanux.Proofs.WG.Queues.RxPollComposition

/-! Both direct source poll sites use the stamped observer. IRQ exit retains
its placement choice and rescans through the actual softirq caller. These are
local caller contracts, not initialized scheduler/Runner or loss-freedom claims. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

theorem BoundaryInv.kernel (hi : BoundaryInv h w) (he : v.k = w.k) : BoundaryInv h v :=
  ⟨hi.audit.kernel he, hi.distinct, hi.released⟩

def napiSoftirq : Obs Unit :=
  RxNapi.softirqWith (audit (auditFocus RxNapi.pendingPrefix)) observePoll

def pollScheduledInline : Obs Unit :=
  RxNapi.inlineWith (audit (auditFocus RxNapi.pendingPrefix)) observePoll

def napiIrqExit : Obs Unit :=
  RxNapi.irqExitWith (audit (auditFocus RxNapi.scheduledPrefix)) napiSoftirq

theorem napiSoftirq_erases : ErasesPrefix napiSoftirq Leanux.Env.napiSoftirq :=
  RxNapi.softirq_erases (audit_erases (auditFocus_erases RxNapi.pending_erases)) observePoll_erases

theorem pollScheduledInline_erases : ErasesPrefix pollScheduledInline Leanux.Env.pollScheduledInline :=
  RxNapi.inline_erases (audit_erases (auditFocus_erases RxNapi.pending_erases)) observePoll_erases

theorem napiIrqExit_erases : ErasesPrefix napiIrqExit Leanux.Env.napiIrqExit :=
  RxNapi.irqExit_erases (audit_erases (auditFocus_erases RxNapi.scheduled_erases)) napiSoftirq_erases

theorem napiSoftirq_preserves : PrefixPreserves BoundaryInv BoundarySafe napiSoftirq :=
  RxNapi.softirq_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he)
    (audit_preserves _ (auditFocus_preserves RxNapi.pending_preserves)) observePoll_preserves

theorem pollScheduledInline_preserves : PrefixPreserves BoundaryInv BoundarySafe pollScheduledInline :=
  RxNapi.inline_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he)
    (audit_preserves _ (auditFocus_preserves RxNapi.pending_preserves)) observePoll_preserves

theorem napiIrqExit_preserves : PrefixPreserves BoundaryInv BoundarySafe napiIrqExit :=
  RxNapi.irqExit_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he)
    (audit_preserves _ (auditFocus_preserves RxNapi.scheduled_preserves)) napiSoftirq_preserves

private theorem poll_allocation (pid : PeerId) (budget : Nat) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (rxPollStackPrefix pid budget) :=
  rxPollStackPrefix_preserves allocationAmbient allocationTx allocationRx allocationWgXmit pid budget

/-- Expanded focus agrees at the same incoming lifetime journal. The proof
uses actual lower append contracts, rather than independent source erasures. -/
theorem napiSoftirq_projects :
    ProjectsUnder AuditInv auditEvent napiSoftirq (auditFocus napiSoftirqPrefix) := by
  have focused := RxNapi.softirq_focus (I := AllocationInv) (S := LifetimeEvent.Safe) (encode := AuditEvent.lifetime) (decode := AuditEvent.lifetime?)
    (fun _ => rfl) (fun _ _ (hi : AllocationInv _ _) => hi.safe)
    (fun _ _ _ he (hi : AllocationInv _ _) => hi.kernel he)
    RxNapi.pending_preserves poll_allocation
    (FocusesUnder.focus RxNapi.pendingPrefix) (fun pid budget => FocusesUnder.focus (rxPollStackPrefix pid budget))
  rw [RxNapi.softirq_cut] at focused
  have projected := RxNapi.softirq_projects (I := AuditInv) (S := AuditSafe) auditEvent
    (fun _ _ (hi : AuditInv _ _) => hi.safe) (fun _ _ _ he (hi : AuditInv _ _) => hi.kernel he)
    (auditFocus_preserves RxNapi.pending_preserves) (fun pid budget => auditFocus_preserves (poll_allocation pid budget))
    (audit_projects (auditFocus_preserves RxNapi.pending_preserves)) observePoll_projects
  intro w h hi
  exact (focused w (h.filterMap auditEvent) hi.1).symm.trans (projected w h hi)

theorem pollScheduledInline_projects :
    ProjectsUnder AuditInv auditEvent pollScheduledInline (auditFocus pollScheduledInlinePrefix) := by
  have focused := RxNapi.inline_focus (I := AllocationInv) (S := LifetimeEvent.Safe) (encode := AuditEvent.lifetime) (decode := AuditEvent.lifetime?)
    (fun _ => rfl) (fun _ _ (hi : AllocationInv _ _) => hi.safe)
    (fun _ _ _ he (hi : AllocationInv _ _) => hi.kernel he)
    RxNapi.pending_preserves poll_allocation
    (FocusesUnder.focus RxNapi.pendingPrefix) (fun pid budget => FocusesUnder.focus (rxPollStackPrefix pid budget))
  rw [RxNapi.inline_cut] at focused
  have projected := RxNapi.inline_projects (I := AuditInv) (S := AuditSafe) auditEvent
    (fun _ _ (hi : AuditInv _ _) => hi.safe) (fun _ _ _ he (hi : AuditInv _ _) => hi.kernel he)
    (auditFocus_preserves RxNapi.pending_preserves) (fun pid budget => auditFocus_preserves (poll_allocation pid budget))
    (audit_projects (auditFocus_preserves RxNapi.pending_preserves)) observePoll_projects
  intro w h hi
  exact (focused w (h.filterMap auditEvent) hi.1).symm.trans (projected w h hi)

theorem napiIrqExit_projects :
    ProjectsUnder AuditInv auditEvent napiIrqExit (auditFocus napiIrqExitPrefix) := by
  have focused := RxNapi.irqExit_focus (I := AllocationInv) (S := LifetimeEvent.Safe) (encode := AuditEvent.lifetime) (decode := AuditEvent.lifetime?)
    (fun _ => rfl) (fun _ _ (hi : AllocationInv _ _) => hi.safe)
    (fun _ _ _ he (hi : AllocationInv _ _) => hi.kernel he)
    RxNapi.scheduled_preserves napiSoftirqPrefix_allocation
    (FocusesUnder.focus RxNapi.scheduledPrefix) (FocusesUnder.focus napiSoftirqPrefix)
  rw [RxNapi.irqExit_cut] at focused
  have projected := RxNapi.irqExit_projects (I := AuditInv) (S := AuditSafe) auditEvent
    (fun _ _ (hi : AuditInv _ _) => hi.safe) (fun _ _ _ he (hi : AuditInv _ _) => hi.kernel he)
    (auditFocus_preserves RxNapi.scheduled_preserves) (auditFocus_preserves napiSoftirqPrefix_allocation)
    (audit_projects (auditFocus_preserves RxNapi.scheduled_preserves)) napiSoftirq_projects
  intro w h hi
  exact (focused w (h.filterMap auditEvent) hi.1).symm.trans (projected w h hi)

end Leanux.Proofs.WG.Queues.RxHistory
