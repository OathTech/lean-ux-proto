import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDeleteSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerDeleteSyscall

/-! The actual deletion syscall retains its entry companions through seccomp
and descriptor setup, then carries the complete ledger through return to user.
No unused traffic callback is assumed for this fixed syscall constructor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Runner.Delete
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal

theorem dispatch : Checked (Driver.dispatchObserved hooks .wgDelete) :=
  rtnetlink _ env_delete

theorem syscall_tail : Checked (do
    let ret ← Driver.dispatchObserved hooks .wgDelete
    for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
    liftPrefix (liftFS taskWorkRun)
    let shape := Net.Fib.shape (← liftPrefix getRouting)
    liftPrefix (modifyAmbient fun w=>{w with extraOut:=w.extraOut++[("fib_trie",shape)]})
    pure ret) := by
  apply Ensures.bind dispatch
  intro ret
  change Product.Checked _
  apply Product.bind_checked
  · apply Product.list
    intro c acc
    exact Product.bind_checked (Product.seccomp (Seccomp.enterHarnessCall c))
      (fun _=>Product.pure_checked (ForInStep.yield ()))
  intro _
  apply Product.bind_checked (Product.fs taskWorkRun)
  intro _
  apply Product.bind_checked routing_read
  intro routing
  apply Product.bind_checked (Product.ambient (modify fun w=>
    {w with extraOut:=w.extraOut++[("fib_trie",Net.Fib.shape routing)]}))
  intro _
  exact Product.pure_checked ret

theorem syscall : Checked (Driver.syscallObserved hooks .wgDelete) := by
  unfold Driver.syscallObserved syscallWith
  apply Ensures.bind (Q:=fun _=>NativeEntry)
  · apply edit; intro w; rfl
  intro _
  apply Ensures.bind (Q:=fun _=>NativeEntry)
  · change Keeps (liftPrefix (modify _ : Leanux.M Unit))
    apply edit; intro w; rfl
  intro _
  apply Ensures.bind (Q:=fun _=>NativeEntry)
  · change Keeps (liftPrefix (modify _ : Leanux.M Unit))
    apply edit; intro w; rfl
  intro _
  simp only [syscallNr,Syscall.isNet]
  apply Ensures.bind current_read
  intro task
  have suffix : Checked _ := syscall_tail
  apply PrefixEnsures.ite
  · intro _
    apply Ensures.bind (ambient (AmbientM.unsupported _))
    intro _
    simpa only [pure_bind] using suffix
  · intro _
    simpa only [pure_bind] using suffix

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Runner.Delete
