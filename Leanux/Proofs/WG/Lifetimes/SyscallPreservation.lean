import Leanux.Proofs.WG.Queues.JointSyscallLifecycle
import Leanux.Proofs.WG.Origins.OwnerControlCalls

/-! Generic invariant and append laws for the existing syscall source.
The seven callbacks remain arbitrary product observers. Raw entry and exit
leaves preserve the seven-field WG store; stopped journals are retained. -/
namespace Leanux.Proofs.WG.Lifetimes.SyscallSource
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Configuration Origins

variable {E : Type} {I : List E → World → Prop} {S : List E → Prop}

private theorem lift_frame (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v) (a : Leanux.M α)
    (frame : SameView (fun w : World => wgStoreView w.wg) a) :
    PrefixPreserves I S (liftPrefix a) :=
  viewLiftPrefix_preserves (fun w : World => wgStoreView w.wg) safe store frame

private theorem lift_fs (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v) (a : FS.M α) :
    PrefixPreserves I S (liftPrefix (liftFS a)) :=
  lift_frame safe store _ (fun s => productFS_spec a (fun w => wgStoreView w.wg = s) (fun _ _ _ _ hi => hi))

private theorem lift_seccomp (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v) (a : Seccomp.M α) :
    PrefixPreserves I S (liftPrefix (liftSeccomp a)) :=
  lift_frame safe store _ (fun s => productSeccomp_spec a (fun w => wgStoreView w.wg = s) (fun _ _ _ _ hi => hi))

private theorem lift_ambient (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v) (a : AmbientM α) :
    PrefixPreserves I S (liftPrefix (liftAmbient a)) :=
  lift_frame safe store _ (fun s => productAmbient_spec a (fun w => wgStoreView w.wg = s) (fun _ _ hi => hi))

private theorem lift_modify (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v) (f : World → World)
    (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) :
    PrefixPreserves I S (liftPrefix (modify f)) :=
  lift_frame safe store _ (fun s => hoare_modify (P := fun w => wgStoreView w.wg = s) f (fun w hi => (same w).trans hi))

macro "syscall_preserve_step " safe:term:max " using " store:term:max : tactic => `(tactic| first
  | owner_outer_callback
  | (current_env_at unsupported; exact lift_ambient $safe $store (AmbientM.unsupported _))
  | (current_env_at liftPrefix; first
      | exact lift_fs $safe $store _
      | exact lift_seccomp $safe $store _
      | exact lift_ambient $safe $store _
      | exact lift_modify $safe $store _ (fun _ => rfl))
  | (current_env_at Pure.pure; exact PrefixPreserves.pure $safe _)
  | (current_env_at Bind.bind; apply PrefixPreserves.bind)
  | (current_env_at ite; apply PrefixPreserves.ite)
  | (current_env_at dite; split)
  | support_intro
  | current_env_match)

private theorem syscall_tail_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v) (call : Syscall) (dispatch : PrefixM E Int)
    (sendWorkers timers route xmit advance cleanup : PrefixM E Unit)
    (hd : PrefixPreserves I S dispatch) (hs : PrefixPreserves I S sendWorkers)
    (ht : PrefixPreserves I S timers) (hr : PrefixPreserves I S route)
    (hx : PrefixPreserves I S xmit) (ha : PrefixPreserves I S advance)
    (hc : PrefixPreserves I S cleanup) :
    PrefixPreserves I S (do
      let ret ← dispatch
      for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
      liftPrefix (liftFS taskWorkRun)
      match call with
      | .wgSet _ | .wgInject .. => sendWorkers; timers
      | .wgUp => sendWorkers; timers; route
      | .wgXmit .. => xmit; timers
      | .wgBatch .. => timers
      | .wgAdvance _ => advance
      | .wgNetnsClose => cleanup
      | _ => pure ()
      match call with
      | .wgUp | .wgDown | .wgDelete | .wgDeladdr _ | .wgDelroute .. | .wgSetMtu _ | .wgNetnsClose
      | .wgAddroute .. | .wgAddaddr .. =>
        let shape := Net.Fib.shape (← liftPrefix getRouting)
        liftPrefix (modifyAmbient fun w => {w with extraOut := w.extraOut ++ [("fib_trie",shape)]})
      | _ => pure ()
      pure ret) := by
  have routing : PrefixPreserves I S (liftPrefix (getRouting : Leanux.M Net.Routing)) :=
    lift_frame safe store _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v run; cases run; rfl)
  apply PrefixPreserves.bind hd
  intro ret
  apply PrefixPreserves.bind
  · apply PrefixPreserves.forIn _ _ _ safe
    intro c acc
    exact (lift_seccomp safe store (Seccomp.enterHarnessCall c)).bind (fun _ => PrefixPreserves.pure safe _)
  · intro _
    apply PrefixPreserves.bind (lift_fs safe store taskWorkRun)
    intro _
    cases call
    all_goals dsimp only
    all_goals repeat' first
      | owner_outer_callback
      | (change PrefixPreserves I S _; current_env_at getRouting; exact routing)
      | syscall_preserve_step safe using store

private theorem syscall_entry_preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v) (call : Syscall) (body : PrefixM E Int)
    (hb : PrefixPreserves I S body) : PrefixPreserves I S (do
  liftPrefix (modify fun w => { w with fs := {w.fs with userOut := none, userFds := none}, seccomp := {w.seccomp with emitted := {}, translatedLen := none} })
  liftPrefix (modifyWG fun g => {g with queuedThisCall := []})
  liftPrefix (modifyAmbient fun a => {a with steps := #[],extraOut := [],fired := #[],netRxSections := 0,netRxSection := 0})
  match syscallNr call with
  | some nr => liftPrefix (liftSeccomp (Seccomp.enterHarnessCall nr))
  | none =>
    if call.isNet && (← liftPrefix getCurrent).seccomp.mode != .disabled then
      liftPrefix (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")
  body) := by
  have current : PrefixPreserves I S (liftPrefix Leanux.getCurrent) := by
    unfold Leanux.getCurrent
    exact lift_fs safe store (StateT.lift TaskM.getCurrent)
  change PrefixPreserves I S _
  apply PrefixPreserves.bind
  · apply lift_modify safe store
    intro w
    rfl
  intro _
  apply PrefixPreserves.bind
  · apply lift_modify safe store
    intro w
    rfl
  intro _
  apply PrefixPreserves.bind
  · apply lift_modify safe store
    intro w
    rfl
  intro _
  cases hn : syscallNr call
  all_goals repeat' first
    | owner_outer_callback
    | (change PrefixPreserves I S _; current_env_at Leanux.getCurrent; exact current)
    | syscall_preserve_step safe using store
    | owner_control_audit_reduce

/-- Exact entry resets, dispatch, wait callbacks and final FIB observation.
Every callback retains its full actual product observer domain. -/
theorem preserves (safe : ∀ h w, I h w → S h)
    (store : ∀ h w v, wgStoreView v.wg = wgStoreView w.wg → I h w → I h v) (call : Syscall) (dispatch : PrefixM E Int)
    (sendWorkers timers route xmit advance cleanup : PrefixM E Unit)
    (hd : PrefixPreserves I S dispatch) (hs : PrefixPreserves I S sendWorkers)
    (ht : PrefixPreserves I S timers) (hr : PrefixPreserves I S route)
    (hx : PrefixPreserves I S xmit) (ha : PrefixPreserves I S advance)
    (hc : PrefixPreserves I S cleanup) :
    PrefixPreserves I S (syscallWith (fun {_} a => liftPrefix a)
      dispatch sendWorkers timers route xmit advance cleanup call) := by
  exact syscall_entry_preserves safe store call _
    (syscall_tail_preserves safe store call dispatch sendWorkers timers route xmit advance cleanup hd hs ht hr hx ha hc)

private theorem appends_true {E α : Type} (a : PrefixM E α) (ha : Appends a) :
    PrefixPreserves (fun _ _ => True) (fun _ => True) a := by
  intro w h _
  obtain ⟨suffix,hs⟩ := ha w h
  refine ⟨suffix,hs,True.intro,?_⟩
  cases (runPrefix a w h).1 <;> trivial

/-- Exact append behavior for arbitrary callbacks and incoming journals,
including source failure after any completed callback. -/
theorem appends (call : Syscall) (dispatch : PrefixM E Int)
    (sendWorkers timers route xmit advance cleanup : PrefixM E Unit)
    (hd : Appends dispatch) (hs : Appends sendWorkers) (ht : Appends timers)
    (hr : Appends route) (hx : Appends xmit) (ha : Appends advance) (hc : Appends cleanup) :
    Appends (syscallWith (fun {_} a => liftPrefix a)
      dispatch sendWorkers timers route xmit advance cleanup call) := by
  have checked := preserves (I := fun _ _ => True) (S := fun _ => True)
    (fun _ _ hi => hi) (fun _ _ _ _ hi => hi) call dispatch
    sendWorkers timers route xmit advance cleanup
    (appends_true _ hd) (appends_true _ hs) (appends_true _ ht)
    (appends_true _ hr) (appends_true _ hx) (appends_true _ ha) (appends_true _ hc)
  intro w h
  obtain ⟨suffix,hs,_,_⟩ := checked w h True.intro
  exact ⟨suffix,hs⟩

end Leanux.Proofs.WG.Lifetimes.SyscallSource
