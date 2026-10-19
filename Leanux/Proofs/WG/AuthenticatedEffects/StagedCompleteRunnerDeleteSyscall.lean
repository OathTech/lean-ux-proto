import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerDeleteFrames

/-! The actual deletion syscall retains its entry companions through seccomp
and descriptor setup, then carries the complete ledger through return to user.
No unused traffic callback is assumed for this fixed syscall constructor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner.DeleteFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal

theorem dispatch : Checked (Driver.dispatchObserved hooks .wgDelete) :=
  rtnetlink _ env_delete

theorem routing_read : CompleteProduct.Checked (liftPrefix (getRouting : Leanux.M Net.Routing)) := by
  apply CompleteProduct.store
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w value v run
  cases run
  rfl

theorem syscall_tail : Checked (do
    let ret ← Driver.dispatchObserved hooks .wgDelete
    for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
    liftPrefix (liftFS taskWorkRun)
    let shape := Net.Fib.shape (← liftPrefix getRouting)
    liftPrefix (modifyAmbient fun w=>{w with extraOut:=w.extraOut++[("fib_trie",shape)]})
    pure ret) := by
  apply PrefixEnsures.bind dispatch
  intro ret
  change CompleteProduct.Checked _
  apply CompleteProduct.bind_checked
  · apply CompleteProduct.list
    intro c acc
    exact CompleteProduct.bind_checked (CompleteProduct.seccomp (Seccomp.enterHarnessCall c))
      (fun _=>CompleteProduct.pure_checked (ForInStep.yield ()))
  intro _
  apply CompleteProduct.bind_checked (CompleteProduct.fs taskWorkRun)
  intro _
  apply CompleteProduct.bind_checked routing_read
  intro routing
  apply CompleteProduct.bind_checked (CompleteProduct.ambient (modify fun w=>
    {w with extraOut:=w.extraOut++[("fib_trie",Net.Fib.shape routing)]}))
  intro _
  exact CompleteProduct.pure_checked ret

theorem current_read : Keeps (liftPrefix (getCurrent : Leanux.M Task)) :=
  fs (StateT.lift TaskM.getCurrent)

theorem syscall : Checked (Driver.syscallObserved hooks .wgDelete) := by
  unfold Driver.syscallObserved syscallWith
  apply PrefixEnsures.bind (Q:=fun _=>Entry)
  · apply edit; intro w; rfl
  intro _
  apply PrefixEnsures.bind (Q:=fun _=>Entry)
  · change Keeps (liftPrefix (modify _ : Leanux.M Unit))
    apply edit; intro w; rfl
  intro _
  apply PrefixEnsures.bind (Q:=fun _=>Entry)
  · change Keeps (liftPrefix (modify _ : Leanux.M Unit))
    apply edit; intro w; rfl
  intro _
  simp only [syscallNr,Syscall.isNet]
  apply PrefixEnsures.bind current_read
  intro task
  have suffix : Checked _ := syscall_tail
  apply PrefixEnsures.ite
  · intro _
    apply PrefixEnsures.bind (ambient (AmbientM.unsupported _))
    intro _
    simpa only [pure_bind] using suffix
  · intro _
    simpa only [pure_bind] using suffix

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner.DeleteFrames
