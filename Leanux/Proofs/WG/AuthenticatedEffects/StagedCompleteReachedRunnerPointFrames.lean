import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerPointSource

/-! Native packet-account frames use the actual returned World and history.
The dispatch entry keeps its native reference/service companions; an arbitrary
packet-account state is never silently promoted to a destructor entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal

def Native.input : {α : Type} → {action : PrefixOuter Event α} → Native action → World
  | _,_,.prefill _ w => w
  | _,_,.boot _ _ w => w
  | _,_,.enter _ w _ => w
  | _,_,.prelude _ w => w
  | _,_,.routing _ w _ => w
  | _,_,.route _ w => w
  | _,_,.cleanup _ w => w
  | _,_,.skip _ w => w

def Native.output : {α : Type} → {action : PrefixOuter Event α} → Native action → α → World
  | _,_,.prefill ..,w => w
  | _,_,.boot ..,w => w
  | _,_,.enter ..,out => out.2
  | _,_,.prelude ..,out => out.2
  | _,_,.routing ..,out => out.2
  | _,_,.route ..,out => out.2
  | _,_,.cleanup ..,out => out.2
  | _,_,.skip ..,out => out.2

def Child.Entry : {α : Type} → {action : PrefixM Event α} → Child action → History → World → Prop
  | _,_,.dispatch _,h,w => CompletePrefix.With CompleteRunner.DeleteFrames.Entry CompleteProduct.Safe h w
  | _,_,.sends,h,w => CompleteProduct.Carrier h w
  | _,_,.idle,h,w => CompleteProduct.Carrier h w
  | _,_,.afterXmit,h,w => CompleteProduct.Carrier h w
  | _,_,.advance,h,w => CompleteProduct.Carrier h w

theorem Child.entry_carrier (token : Child action) (before : token.Entry h w) :
    CompleteProduct.Carrier h w := by
  cases token with
  | dispatch => exact before.1.1
  | sends => exact before
  | idle => exact before
  | afterXmit => exact before
  | advance => exact before

theorem runAt_normal {action : PrefixM Event α}
    (performed : runPrefixOuter (runAtPrefix index w action) h=(.ok out,last)) :
    runPrefix action w h=(.ok out,last) := by
  rw [runAtPrefix_run] at performed
  cases source : runPrefix action w h with
  | mk result history =>
    rw [source] at performed
    cases result <;> cases performed
    rfl

theorem checked_normal {action : PrefixM Event α}
    (checked : PrefixEnsures P S action Q) (before : P h w)
    (performed : runPrefixOuter (runAtPrefix index w action) h=(.ok out,last)) :
    Q out.1 last out.2 := by
  obtain ⟨_,_,_,post⟩ := checked w h before
  simpa only [runAt_normal performed] using post

theorem Child.normal (token : Child action) (before : token.Entry h w)
    (performed : runPrefixOuter (runAtPrefix index w action) h=(.ok out,last)) :
    CompleteProduct.Carrier last out.2 := by
  cases token with
  | dispatch call =>
    exact (checked_normal (RunnerSource.dispatch_checked call) before performed).1
  | sends => exact checked_normal CompleteProduct.Execution.sends before performed
  | idle => exact checked_normal CompleteProduct.Execution.idle before performed
  | afterXmit => exact checked_normal CompleteProduct.Execution.after_xmit before performed
  | advance => exact checked_normal CompleteProduct.Execution.advance before performed

private theorem enter_frame (call : Syscall) : CompleteProduct.Checked (SyscallSource.enter call) := by
  unfold SyscallSource.enter
  apply CompleteProduct.bind_checked
  · apply CompleteProduct.edit; intro w; rfl
  intro _
  apply CompleteProduct.bind_checked
  · change CompleteProduct.Checked (liftPrefix (modify _ : Leanux.M Unit))
    apply CompleteProduct.edit; intro w; rfl
  intro _
  apply CompleteProduct.bind_checked (CompleteProduct.ambient _)
  intro _
  split
  · exact CompleteProduct.seccomp _
  · apply CompleteProduct.bind_checked
    · exact CompleteProduct.fs (StateT.lift TaskM.getCurrent)
    intro task
    split
    · exact CompleteProduct.ambient (AmbientM.unsupported _)
    · exact CompleteProduct.pure_checked _

private theorem routing_frame (call : Syscall) : CompleteProduct.Checked (ReturnSource.routing call) := by
  cases call <;> unfold ReturnSource.routing
  all_goals first
    | exact CompleteProduct.pure_checked _
    | exact CompleteProduct.bind_checked CompleteRunner.DeleteFrames.routing_read
        (fun _=>CompleteProduct.ambient _)

theorem Native.normal (token : Native action) (before : CompleteProduct.Carrier h token.input)
    (performed : runPrefixOuter action h=(.ok out,last)) :
    CompleteProduct.Carrier last (token.output out) := by
  cases token with
  | prefill count w =>
    have quiet := CompleteRunner.prefill_quiet (E:=Event) count w h
    rw [performed] at quiet
    change last=h at quiet
    subst last
    exact CompleteProduct.store_transport h w out (CompleteRunner.prefill_store count w out performed) before
  | boot net foreign w =>
    have quiet := CompleteRunner.boot_quiet (E:=Event) net foreign w h
    rw [performed] at quiet
    change last=h at quiet
    subst last
    exact CompleteProduct.store_transport h w out (CompleteRunner.boot_store net foreign w out performed) before
  | enter index w call => exact checked_normal (enter_frame call) before performed
  | prelude index w =>
    apply checked_normal (P:=CompleteProduct.Carrier) (S:=CompleteProduct.Safe) (Q:=fun _=>CompleteProduct.Carrier) (action:=ReturnSource.prelude) _ before performed
    unfold ReturnSource.prelude
    apply CompleteProduct.bind_checked
    · apply CompleteProduct.list
      intro c acc
      exact CompleteProduct.bind_checked (CompleteProduct.seccomp _) (fun _=>CompleteProduct.pure_checked _)
    intro _
    exact CompleteProduct.fs _
  | routing index w call => exact checked_normal (routing_frame call) before performed
  | route index w =>
    exact checked_normal (CompleteProduct.product_store _ Framing.routeIntoWg0_sameKernel) before performed
  | cleanup index w => exact checked_normal CompleteProduct.cleanup before performed
  | skip index w => exact checked_normal (CompleteProduct.ambient AmbientM.skipAmbient) before performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
