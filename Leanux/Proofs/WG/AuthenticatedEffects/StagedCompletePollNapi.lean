import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePollConcrete
import Leanux.Proofs.WG.Queues.RxNapiCuts

/-! Both original NAPI dispatch modes and IRQ exit use the concrete paired
poll proof. Native scheduling metadata retains the actual packet ledger;
selected stopped cuts keep the same CompleteTransmit safety alternative. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePollNapi
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal CompletePoll
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}

private theorem pending_frame : SameView StagedEntry.view RxNapi.pendingSource := by
  unfold RxNapi.pendingSource
  apply SameView.bind (TimerFrames.store getDev_sameWGStore)
  intro d
  exact SameView.pure _ _

private theorem scheduled_frame : SameView StagedEntry.view RxNapi.scheduledSource := by
  unfold RxNapi.scheduledSource
  apply SameView.bind (TimerFrames.store getDev_sameWGStore)
  intro d
  exact SameView.pure _ _

private theorem pending : Checked debts locals (CompleteTransmit.Safe debts)
    (liftWGObserver (liftWGPrefix RxNapi.pendingSource)) :=
  CompletePoll.state _ (CompletePassive.native _
    (fun ledger => CompleteTransmit.Safe.accounted ledger locals) _ pending_frame)

private theorem scheduled : Checked debts locals (CompleteTransmit.Safe debts)
    (liftWGObserver (liftWGPrefix RxNapi.scheduledSource)) :=
  CompletePoll.state _ (CompletePassive.native _
    (fun ledger => CompleteTransmit.Safe.accounted ledger locals) _ scheduled_frame)

theorem softirq : Checked debts locals (CompleteTransmit.Safe debts) (Driver.softirqObserved hooks) :=
  RxNapi.softirq_preserves (I := Carrier debts locals) CompletePollConcrete.safe CompleteStack.stable
    pending CompletePollConcrete.native_poll

theorem inline_poll : Checked debts locals (CompleteTransmit.Safe debts) (Driver.inlinePollObserved hooks) :=
  RxNapi.inline_preserves (I := Carrier debts locals) CompletePollConcrete.safe CompleteStack.stable
    pending CompletePollConcrete.native_poll

theorem irq_exit : Checked debts locals (CompleteTransmit.Safe debts) (Driver.irqExitObserved hooks) :=
  RxNapi.irqExit_preserves (I := Carrier debts locals) CompletePollConcrete.safe CompleteStack.stable
    scheduled softirq

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePollNapi
