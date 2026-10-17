import Leanux.Proofs.WG.Queues.GroSource
import Leanux.Proofs.WG.Queues.RxPollStampSafety

/-! One literal poll body with the old atomic observers embedded into a larger
journal and arbitrary product GRO callbacks. No poll, getter or receipt is
re-executed; the old specialization is definitionally the original observer. -/
namespace Leanux.Proofs.WG.Queues.RxJoint.PollSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

variable {E F : Type}

def pollWith (old : {α : Type} → Obs α → PrefixM E α)
    (receive : Gro → Entry → PrefixM E Gro) (flushAll : Gro → PrefixM E Unit)
    (pid : PeerId) (budget : Nat) : PrefixM E Nat := do
  if ← liftPrefix (branch .rxPollNoBudget (budget == 0)) then return 0
  let mut workDone := 0
  let mut gro : Gro := {}
  let mut drained := false
  for _ in [0:MAX_QUEUED_PACKETS + 1] do
    let first ← old (access (liftWGObserver (peekAccess pid)))
    let go ← old (access (liftWGObserver (readyAccess first)))
    if !go then
      drained := true
      break
    let some id := first | liftPrefix (invariant "unreachable")
    let captured ← old (capture id)
    let pkt := captured.1
    if pkt.peer != pid then liftPrefix (invariant "a packet on another peer's rx_queue")
    old (drop pid workDone id captured.2)
    let mut free := true
    if !(← old (receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
        (Event.checkedState workDone id captured.2 pkt))) then
      if !(← liftPrefix (branch .rxPollCounterInvalid !(← old (receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
          (Event.checkedCounter workDone id captured.2 pkt))))) then
        let endpoint ← old (receiptObserved (liftPrefix (liftWG (endpointFromSkb pkt.source)))
          (Event.checkedEndpoint workDone id captured.2 pkt))
        if !(← liftPrefix (branch .rxPollEndpointFailed endpoint.isNone)) then
          let some e := endpoint | liftPrefix (invariant "unreachable")
          for entry in (← old (consume pid workDone id captured.2 pkt e)).toList do
            gro ← receive gro entry
          free := false
    old (access (liftWGObserver (keypairPutPrefix (some pkt.keypair) false)))
    old (access (liftWGObserver (peerPutMixed (some pid))))
    _ ← liftPrefix (branch .rxPollFree free)
    old (access (liftWGObserver (freeRxSkbPrefix id)))
    workDone := workDone + 1
    if ← liftPrefix (branch .rxPollBudgetDone (workDone ≥ budget)) then break
  if !drained && workDone < budget then liftPrefix (invariant "the rx_queue did not drain")
  if ← liftPrefix (branch .rxPollComplete (workDone < budget)) then
    old (access (liftWGObserver (completeAccess pid)))
    flushAll gro
  else liftPrefix (unsupported "a NAPI poll that used its whole budget (a repoll)")
  return workDone

theorem poll_factor (pid : PeerId) (budget : Nat) :
    poll pid budget = pollWith (fun {_} a => a) RxJoint.receive RxJoint.flushAll pid budget := rfl

/-- Guard applications by their actual source head before attempting a checked
composition rule. No rule or goal is solved by this recognizer. -/
elab "poll_source_head " name:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := target.getAppArgs
  let action ←
    if target.isAppOf ``ProjectsPrefix then
      if args.size ≥ 2 then pure args[args.size - 2]! else Lean.throwError "missing observer"
    else if target.isAppOf ``Appends then
      if args.size > 0 then pure args.back! else Lean.throwError "missing observer"
    else Lean.throwError "not a poll projection or append contract"
  let head := action.consumeMData.getAppFn
  let actual ← match head with
    | .const n _ => pure n.toString
    | .fvar f => pure (← f.getDecl).userName.eraseMacroScopes.toString
    | _ => Lean.throwError "not a named source head"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual == expected || actual.endsWith ("." ++ expected) do
    Lean.throwError "different source head"

/-- Only append-only original atomic observers are embedded. This premise is
satisfied by canonical focus and does not assume arbitrary observers ignore or
preserve their incoming histories. -/
theorem poll_projects (ρ : E → Option F)
    (old : {α : Type} → Obs α → PrefixM E α)
    (old' : {α : Type} → Obs α → PrefixM F α)
    (receive : Gro → Entry → PrefixM E Gro) (receive' : Gro → Entry → PrefixM F Gro)
    (flushAll : Gro → PrefixM E Unit) (flushAll' : Gro → PrefixM F Unit)
    (ho : ∀ {α : Type} (a : Obs α), Appends a → ProjectsPrefix ρ id (old a) (old' a))
    (hr : ∀ g e, ProjectsPrefix ρ id (receive g e) (receive' g e))
    (hf : ∀ g, ProjectsPrefix ρ id (flushAll g) (flushAll' g))
    (pid : PeerId) (budget : Nat) :
    ProjectsPrefix ρ id (pollWith old receive flushAll pid budget)
      (pollWith old' receive' flushAll' pid budget) := by
  unfold pollWith
  apply projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _)
  intro noBudget
  dsimp only [id]
  apply projectsPrefix_ite
  · intro _
    exact projectsPrefix_pure ρ id 0
  · intro _
    repeat' first
      | (poll_source_head old; apply ho)
      | (poll_source_head receive; exact hr _ _)
      | (poll_source_head flushAll; exact hf _)
      | (poll_source_head receiptObserved; apply Appends.receiptObserved)
      | (poll_source_head capture; exact capture_appends _)
      | (poll_source_head consume; exact consume_appends _ _ _ _ _ _)
      | (poll_source_head access; exact access_appends _)
      | (poll_source_head drop; unfold drop; exact (access_appends _).bind (fun _ => emit_appends _))
      | (poll_source_head liftPrefix; first
          | exact Appends.lift _
          | exact projectsPrefix_lift ρ _)
      | (poll_source_head Pure.pure; first
          | exact projectsPrefix_pure ρ id _
          | exact projectsPrefix_pure ρ (projectStep id) _)
      | (poll_source_head ForIn.forIn; first
          | apply projectsPrefix_range ρ id
          | apply projectsPrefix_forIn ρ id)
      | (poll_source_head Bind.bind; first
          | apply projectsPrefix_bind ρ id id
          | apply projectsPrefix_bind ρ id (projectStep id))
      | (poll_source_head ite; apply projectsPrefix_ite)
      | dsimp only [id]
      | maintenance_intro
      | (poll_source_head ite; split)
      | (poll_source_head dite; split)
      | (with_reducible split)

    all_goals
      exfalso
      simp_all only [id]
      rename_i impossible _
      exact impossible _ rfl

/-- The new journal grows from its actual arbitrary incoming history whenever
its old-atom embedding and its actual GRO callbacks do. -/
theorem poll_appends (old : {α : Type} → Obs α → PrefixM E α)
    (receive : Gro → Entry → PrefixM E Gro) (flushAll : Gro → PrefixM E Unit)
    (ho : ∀ {α : Type} (a : Obs α), Appends a → Appends (old a))
    (hr : ∀ g e, Appends (receive g e)) (hf : ∀ g, Appends (flushAll g))
    (pid : PeerId) (budget : Nat) : Appends (pollWith old receive flushAll pid budget) := by
  unfold pollWith
  repeat' first
    | (poll_source_head old; apply ho)
    | (poll_source_head receive; exact hr _ _)
    | (poll_source_head flushAll; exact hf _)
    | (poll_source_head receiptObserved; apply Appends.receiptObserved)
    | (poll_source_head capture; exact capture_appends _)
    | (poll_source_head consume; exact consume_appends _ _ _ _ _ _)
    | (poll_source_head access; exact access_appends _)
    | (poll_source_head drop; unfold drop; exact (access_appends _).bind (fun _ => emit_appends _))
    | (poll_source_head liftPrefix; exact Appends.lift _)
    | (poll_source_head Pure.pure; exact Appends.pure _)
    | (poll_source_head ForIn.forIn; first | apply Appends.range | apply Appends.forIn)
    | (poll_source_head Bind.bind; apply Appends.bind)
    | maintenance_intro
    | dsimp only
    | split

/-- Canonical focus supplies the atomic embedding premise using each original
atom's checked append contract. The entire old poll, including a failed prefix,
is recovered under the supplied callback projections. -/
theorem focused_projects (encode : Event → E) (ρ : E → Option Event)
    (he : ∀ e, ρ (encode e) = some e)
    (receive : Gro → Entry → PrefixM E Gro) (flushAll : Gro → PrefixM E Unit)
    (hr : ∀ g e, ProjectsPrefix ρ id (receive g e) (RxJoint.receive g e))
    (hf : ∀ g, ProjectsPrefix ρ id (flushAll g) (RxJoint.flushAll g))
    (pid : PeerId) (budget : Nat) :
    ProjectsPrefix ρ id (pollWith (fun {_} a => focusPrefix encode ρ a) receive flushAll pid budget)
      (poll pid budget) := by
  rw [poll_factor]
  exact poll_projects ρ _ _ receive RxJoint.receive flushAll RxJoint.flushAll
    (fun a ha => ha.project_focus encode ρ he) hr hf pid budget

end Leanux.Proofs.WG.Queues.RxJoint.PollSource
