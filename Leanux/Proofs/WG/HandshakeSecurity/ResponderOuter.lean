import Leanux.Proofs.WG.HandshakeSecurity.ResponderIngress

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.Outer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Configuration CurrentEnvironment

private theorem safe (h : List RxHistory.Event) (w : World) (hi : Joint.Inv h w) :
    Joint.Safe h := hi.safe

/-- The live-state part observes WG store fields; saved checks continue to refer
only to the immutable historical worlds already in the incoming journal. -/
theorem store (h : List RxHistory.Event) (w v : World)
    (eq : wgStoreView v.wg = wgStoreView w.wg) (hi : Joint.Inv h w) : Joint.Inv h v := by
  have kept : Global.Inv h {w with wg := v.wg} :=
    Global.store h w _ (by simp only [productStoreView,eq]) hi.2
  exact ⟨PublicationOuter.store h w v eq hi.1,kept⟩

theorem lift_spec (a : Leanux.M α)
    (ha : ∀ h, Preserves (Joint.Inv h) a) : Joint.Preserves (liftPrefix a) :=
  (PrefixEnsures.lift a safe (fun h w x v hi hr => (hoare_iff_run _ _ _).mp (ha h) w x v hi hr)).preserves

theorem lift_store (a : Leanux.M α) (ha : SameProductStore a) :
    Joint.Preserves (liftPrefix a) := Joint.lift_store a ha

theorem lift_wgStore (a : Leanux.M α)
    (ha : SameView (fun w : World => wgStoreView w.wg) a) :
    Joint.Preserves (liftPrefix a) := by
  apply lift_spec
  intro h
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  exact store h w v ((ProjectedAction.iff_run _ _ _).mp ha w x v hr) hi

theorem lift_fs (a : FS.M α) : Joint.Preserves (liftPrefix (liftFS a)) :=
  lift_spec _ (fun h => productFS_spec a (Joint.Inv h) (fun w _ _ _ hi => store h w _ rfl hi))

theorem lift_task (a : TaskM α) : Joint.Preserves (liftPrefix (liftTask a)) :=
  lift_spec _ (fun h => productTask_spec a (Joint.Inv h) (fun w _ _ hi => store h w _ rfl hi))

theorem lift_ambient (a : AmbientM α) : Joint.Preserves (liftPrefix (liftAmbient a)) :=
  lift_spec _ (fun h => productAmbient_spec a (Joint.Inv h) (fun w _ hi => store h w _ rfl hi))

theorem lift_seccomp (a : Seccomp.M α) : Joint.Preserves (liftPrefix (liftSeccomp a)) :=
  lift_spec _ (fun h => productSeccomp_spec a (Joint.Inv h) (fun w _ _ _ hi => store h w _ rfl hi))

theorem lift_get : Joint.Preserves (liftPrefix (get : Leanux.M World)) :=
  lift_spec _ (fun _ => hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2))

theorem lift_modify (f : World → World) (same : ∀ w, wgStoreView (f w).wg = wgStoreView w.wg) :
    Joint.Preserves (liftPrefix (modify f)) :=
  lift_spec _ (fun h => hoare_modify _ (fun w hi => store h w (f w) (same w) hi))

macro "responder_outer_step" : tactic => `(tactic| first
  | (change PrefixPreserves Joint.Inv Joint.Safe _; current_env_at unsupported; exact lift_ambient (AmbientM.unsupported _))
  | (change PrefixPreserves Joint.Inv Joint.Safe _; current_env_at skipCut; exact lift_ambient (AmbientM.skipCut _))
  | (change PrefixPreserves Joint.Inv Joint.Safe _; current_env_at liftPrefix; first
      | exact lift_fs _
      | exact lift_task _
      | exact lift_ambient _
      | exact lift_seccomp _
      | exact lift_get
      | exact lift_modify _ (fun _ => rfl))
  | (change PrefixPreserves Joint.Inv Joint.Safe _; current_env_at Pure.pure; exact PrefixPreserves.pure safe _)
  | (change PrefixPreserves Joint.Inv Joint.Safe _; current_env_at Bind.bind; apply PrefixPreserves.bind)
  | (change PrefixPreserves Joint.Inv Joint.Safe _; current_env_at ite; apply PrefixPreserves.ite)
  | (change PrefixPreserves Joint.Inv Joint.Safe _; current_env_at dite; split)
  | (maintenance_intro; try dsimp only)
  | (change PrefixPreserves Joint.Inv Joint.Safe _; current_env_match))

/-- The callback is an arbitrary actual product observer, including its Stops.
Descriptor failure returns before calling it, exactly as in the source. -/
theorem socketCallOn (fd : Nat) (body : RxHistory.Obs Int)
    (hb : Joint.Preserves body) :
    Joint.Preserves (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  change PrefixPreserves Joint.Inv Joint.Safe _
  unfold socketCallOnWith
  apply PrefixPreserves.bind (lift_fs (fdget fd))
  intro f
  apply PrefixPreserves.ite
  · intro _; exact PrefixPreserves.pure safe _
  · intro _
    exact hb.bind (fun ret => (lift_fs (fdput f)).bind (fun _ => PrefixPreserves.pure safe ret))

theorem netlinkRequest (body : RxHistory.Obs Int) (hb : Joint.Preserves body) :
    Joint.Preserves (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold netlinkRequestWith
  apply PrefixPreserves.bind
    (socketCallOn _ _ ((lift_ambient (AmbientM.skipCut allocCuts)).bind
      (fun _ => hb.bind (fun ret => (lift_ambient (AmbientM.skipCut allocCuts)).bind
        (fun _ => PrefixPreserves.pure safe ret)))))
  intro ret
  exact (socketCallOn _ _ (PrefixPreserves.pure safe 0)).bind (fun _ => PrefixPreserves.pure safe ret)

theorem rtnetlinkRequest (body : RxHistory.Obs Int) (hb : Joint.Preserves body) :
    Joint.Preserves (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  change PrefixPreserves Joint.Inv Joint.Safe _
  unfold rtnetlinkRequestWith
  repeat' first
    | exact hb
    | (change PrefixPreserves Joint.Inv Joint.Safe _; current_env_at socketCallOnWith; apply socketCallOn)
    | responder_outer_step


private theorem syscall_tail_preserves (call : Syscall) (dispatch : RxHistory.Obs Int)
    (sendWorkers timers route xmit advance cleanup : RxHistory.Obs Unit)
    (hd : Joint.Preserves dispatch) (hs : Joint.Preserves sendWorkers)
    (ht : Joint.Preserves timers) (hr : Joint.Preserves route)
    (hx : Joint.Preserves xmit) (ha : Joint.Preserves advance)
    (hc : Joint.Preserves cleanup) :
    Joint.Preserves (do
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
  have routing : Joint.Preserves (liftPrefix (getRouting : Leanux.M Net.Routing)) :=
    lift_store _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v run; cases run; rfl)
  apply PrefixPreserves.bind hd
  intro ret
  apply PrefixPreserves.bind
  · apply PrefixPreserves.forIn _ _ _ safe
    intro c acc
    exact (lift_seccomp (Seccomp.enterHarnessCall c)).bind (fun _ => PrefixPreserves.pure safe _)
  · intro _
    apply PrefixPreserves.bind (lift_fs taskWorkRun)
    intro _
    cases call
    all_goals dsimp only
    all_goals repeat' first
      | owner_outer_callback
      | (change PrefixPreserves Joint.Inv Joint.Safe _; current_env_at getRouting; exact routing)
      | responder_outer_step

private theorem syscall_entry_preserves (call : Syscall) (body : RxHistory.Obs Int)
    (hb : Joint.Preserves body) : Joint.Preserves (do
  liftPrefix (modify fun w => { w with fs := {w.fs with userOut := none, userFds := none}, seccomp := {w.seccomp with emitted := {}, translatedLen := none} })
  liftPrefix (modifyWG fun g => {g with queuedThisCall := []})
  liftPrefix (modifyAmbient fun a => {a with steps := #[],extraOut := [],fired := #[],netRxSections := 0,netRxSection := 0})
  match syscallNr call with
  | some nr => liftPrefix (liftSeccomp (Seccomp.enterHarnessCall nr))
  | none =>
    if call.isNet && (← liftPrefix getCurrent).seccomp.mode != .disabled then
      liftPrefix (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")
  body) := by
  have current : Joint.Preserves (liftPrefix Leanux.getCurrent) := by
    unfold Leanux.getCurrent
    exact lift_fs (StateT.lift TaskM.getCurrent)
  change PrefixPreserves Joint.Inv Joint.Safe _
  apply PrefixPreserves.bind
  · apply lift_modify
    intro w
    rfl
  intro _
  apply PrefixPreserves.bind
  · apply lift_modify
    intro w
    rfl
  intro _
  apply PrefixPreserves.bind
  · apply lift_modify
    intro w
    rfl
  intro _
  cases hn : syscallNr call
  all_goals repeat' first
    | owner_outer_callback
    | (change PrefixPreserves Joint.Inv Joint.Safe _; current_env_at Leanux.getCurrent; exact current)
    | responder_outer_step
    | owner_control_audit_reduce

/-- Exact entry resets, dispatch, wait callbacks and final FIB observation.
Every callback retains its full actual product observer domain. -/
theorem syscallWith_preserves (call : Syscall) (dispatch : RxHistory.Obs Int)
    (sendWorkers timers route xmit advance cleanup : RxHistory.Obs Unit)
    (hd : Joint.Preserves dispatch) (hs : Joint.Preserves sendWorkers)
    (ht : Joint.Preserves timers) (hr : Joint.Preserves route)
    (hx : Joint.Preserves xmit) (ha : Joint.Preserves advance)
    (hc : Joint.Preserves cleanup) :
    Joint.Preserves (syscallWith (fun {_} a => liftPrefix a)
      dispatch sendWorkers timers route xmit advance cleanup call) := by
  exact syscall_entry_preserves call _
    (syscall_tail_preserves call dispatch sendWorkers timers route xmit advance cleanup hd hs ht hr hx ha hc)

abbrev Audited (g : AuditM α) :=
  FocusedInvariant Joint.Inv Joint.Safe RxHistory.Event.audit RxHistory.auditEvent g

theorem audit_lift (a : Leanux.M α) (ha : Joint.Preserves (liftPrefix a)) :
    Audited (liftPrefix a) := FocusedInvariant.lift _ _ a ha

theorem audit_socket (fd : Nat) (body : AuditM Int) (append : Appends body)
    (hb : Joint.Preserves (RxHistory.audit body)) :
    Joint.Preserves (RxHistory.audit (socketCallOnAudit fd body)) := by
  rw [socketCallOnAudit_factor]
  apply prefixPreserves_congr (socketCallOn fd _ hb)
  intro w h
  exact socketCallOnWith_focuses RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    fd (FocusesUnder.focus body) append w h True.intro

theorem audit_netlink (body : AuditM Int) (hb : Audited body) :
    Joint.Preserves (RxHistory.audit (netlinkRequestAudit body)) := by
  rw [netlinkRequestAudit_factor]
  unfold RxHistory.audit
  rw [← netlinkRequestWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl) body hb.1]
  exact netlinkRequest _ hb.2

theorem socket_audited (fd : Nat) (body : AuditM Int) (hb : Audited body) :
    Audited (socketCallOnAudit fd body) := by
  refine ⟨?_,audit_socket fd body hb.1 hb.2⟩
  rw [socketCallOnAudit_factor]
  exact socketCallOnWith_appends fd hb.1

theorem netlink_audited (body : AuditM Int) (hb : Audited body) :
    Audited (netlinkRequestAudit body) := by
  refine ⟨?_,audit_netlink body hb⟩
  rw [netlinkRequestAudit_factor]
  exact netlinkRequestWith_appends hb.1

theorem rtnetlink_audited (body : AuditM Int) (hb : Audited body) :
    Audited (rtnetlinkRequestAudit body) := by
  refine ⟨?_,?_⟩
  · rw [rtnetlinkRequestAudit_factor]
    exact rtnetlinkRequestWith_appends hb.1
  · rw [rtnetlinkRequestAudit_factor]
    rw [← rtnetlinkRequestWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl) body hb.1]
    exact rtnetlinkRequest _ hb.2

macro "responder_outer_audit_steps" : tactic => `(tactic|
  (change FocusedInvariant Joint.Inv Joint.Safe
      RxHistory.Event.audit RxHistory.auditEvent _
   first
   | (owner_control_audit_at getDev; exact audit_lift _ (lift_store _ (liftWG_sameProductStore _ getDev_sameWGStore)))
   | (owner_control_audit_at mayHaveSlept; exact audit_lift _ (lift_store _ (liftWG_sameProductStore _ mayHaveSlept_sameWGStore)))
   | (owner_control_audit_at getWG; exact audit_lift _ (lift_store _ (fun initial => productGetWG_spec (fun s => s = initial))))
   | (owner_control_audit_at getRouting
      exact audit_lift _ (lift_store _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v hr; cases hr; rfl)))
   | (owner_control_audit_at modifyEnv; exact audit_lift _ (lift_modify _ (fun _ => rfl)))
   | (owner_control_audit_at modifyRouting
      exact audit_lift _ (lift_store _ (fun initial => productRouting_spec _ (fun s => s = initial))))
   | (owner_control_audit_at liftM
      exact audit_lift _ (lift_store _ (fun initial => productRouting_spec _ (fun s => s = initial))))
   | (owner_control_audit_at liftPrefix
      apply audit_lift
      simp only [hidden,peekUnit,resolveUnit,modifyAmbient,unsupported,skipCut]
      exact lift_ambient _)
   | (owner_control_audit_at Pure.pure; exact FocusedInvariant.pure _ _ safe _)
   | (owner_control_audit_at Bind.bind; apply FocusedInvariant.bind
       (encode := RxHistory.Event.audit) (decode := RxHistory.auditEvent) (fun _ => rfl))
   | (owner_control_audit_at ite; apply FocusedInvariant.ite)
   | owner_control_audit_reduce
   | support_intro))

end Leanux.Proofs.WG.HandshakeSecurity.Responder.Outer
