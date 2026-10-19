import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixReceiveConcrete
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixReceiveNapiFrames

/-! Both original NAPI dispatch modes and IRQ exit use the concrete paired
poll proof. Native scheduling metadata retains the actual packet ledger;
selected stopped cuts keep the same CompleteTransmit safety alternative. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ReceiveNapi
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal ReceivePoll
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}

private theorem pending : Checked debts locals CompleteProduct.Safe
    (liftWGObserver (liftWGPrefix RxNapi.pendingSource)) :=
  ReceivePoll.state _ (Passive.native _
    Transmit.account _ ReceiveNapiFrames.pending_frame)

private theorem scheduled : Checked debts locals CompleteProduct.Safe
    (liftWGObserver (liftWGPrefix RxNapi.scheduledSource)) :=
  ReceivePoll.state _ (Passive.native _
    Transmit.account _ ReceiveNapiFrames.scheduled_frame)

theorem softirq : Checked debts locals CompleteProduct.Safe (Driver.softirqObserved hooks) :=
  RxNapi.softirq_preserves (I := With (Carrier debts locals) CompleteProduct.Safe) ReceiveConcrete.safe (ReceiveStack.stable CompleteProduct.Safe)
    pending ReceiveConcrete.native_poll

theorem inline_poll : Checked debts locals CompleteProduct.Safe (Driver.inlinePollObserved hooks) :=
  RxNapi.inline_preserves (I := With (Carrier debts locals) CompleteProduct.Safe) ReceiveConcrete.safe (ReceiveStack.stable CompleteProduct.Safe)
    pending ReceiveConcrete.native_poll

theorem irq_exit : Checked debts locals CompleteProduct.Safe (Driver.irqExitObserved hooks) :=
  RxNapi.irqExit_preserves (I := With (Carrier debts locals) CompleteProduct.Safe) ReceiveConcrete.safe (ReceiveStack.stable CompleteProduct.Safe)
    scheduled softirq

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ReceiveNapi
