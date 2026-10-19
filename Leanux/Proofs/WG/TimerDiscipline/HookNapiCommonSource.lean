import Leanux.Proofs.WG.TimerDiscipline.HookCommonSource
import Leanux.Proofs.WG.TimerDiscipline.ReceiveHookPollSource
import Leanux.Proofs.WG.TimerDiscipline.HandshakeJournalAppendSource

/-! Concrete poll and NAPI callbacks in the common session/hook journal.
Native inner delivery can queue later work; the scheduler observes its dispatch. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Leanux Leanux.WG Leanux.Proofs.Logged HandshakeJournal

theorem receive_appends : Appends receive :=
  HandshakeJournal.step_appends.liftWGObserver

def poll (pid : PeerId) (budget : Nat) : Obs Nat :=
  ReceiveHookPoll.pollWith consume stack pid budget
def softirq : Obs Unit := ReceiveHookPoll.softirqWith consume stack
def inline : Obs Unit := ReceiveHookPoll.inlineWith consume stack
def irqExit : Obs Unit := ReceiveHookPoll.irqExitWith consume stack

theorem poll_erases (pid : PeerId) (budget : Nat) : ErasesPrefix (poll pid budget) (rxPoll pid budget (fun packets=>packets.forM Env.deliverInner)) :=
  ReceiveHookPoll.pollWith_erases consume stack consume_erases stack_erases pid budget
theorem poll_valid (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (poll pid budget) :=
  ReceiveHookPoll.pollWith_valid consume stack ValidHistory consume_valid
    (stack_preserves ValidHistory) pid budget
theorem poll_paired (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun h _=>Paired h) Paired (poll pid budget) :=
  ReceiveHookPoll.pollWith_valid consume stack Paired consume_paired
    (stack_preserves Paired) pid budget
theorem poll_appends (pid : PeerId) (budget : Nat) : Appends (poll pid budget) :=
  ReceiveHookPoll.pollWith_appends consume stack consume_appends stack_appends pid budget

theorem softirq_erases : ErasesPrefix (softirq) Env.napiSoftirq :=
  ReceiveHookPoll.softirqWith_erases consume stack consume_erases stack_erases
theorem softirq_valid :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (softirq) :=
  ReceiveHookPoll.softirqWith_valid consume stack ValidHistory consume_valid
    (stack_preserves ValidHistory)
theorem softirq_paired :
    PrefixPreserves (fun h _=>Paired h) Paired (softirq) :=
  ReceiveHookPoll.softirqWith_valid consume stack Paired consume_paired
    (stack_preserves Paired)
theorem softirq_appends : Appends (softirq) :=
  ReceiveHookPoll.softirqWith_appends consume stack consume_appends stack_appends

theorem inline_erases : ErasesPrefix (inline) Env.pollScheduledInline :=
  ReceiveHookPoll.inlineWith_erases consume stack consume_erases stack_erases
theorem inline_valid :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (inline) :=
  ReceiveHookPoll.inlineWith_valid consume stack ValidHistory consume_valid
    (stack_preserves ValidHistory)
theorem inline_paired :
    PrefixPreserves (fun h _=>Paired h) Paired (inline) :=
  ReceiveHookPoll.inlineWith_valid consume stack Paired consume_paired
    (stack_preserves Paired)
theorem inline_appends : Appends (inline) :=
  ReceiveHookPoll.inlineWith_appends consume stack consume_appends stack_appends

theorem irqExit_erases : ErasesPrefix (irqExit) Env.napiIrqExit :=
  ReceiveHookPoll.irqExitWith_erases consume stack consume_erases stack_erases
theorem irqExit_valid :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (irqExit) :=
  ReceiveHookPoll.irqExitWith_valid consume stack ValidHistory consume_valid
    (stack_preserves ValidHistory)
theorem irqExit_paired :
    PrefixPreserves (fun h _=>Paired h) Paired (irqExit) :=
  ReceiveHookPoll.irqExitWith_valid consume stack Paired consume_paired
    (stack_preserves Paired)
theorem irqExit_appends : Appends (irqExit) :=
  ReceiveHookPoll.irqExitWith_appends consume stack consume_appends stack_appends

end Leanux.Proofs.WG.TimerDiscipline.HookCommon
