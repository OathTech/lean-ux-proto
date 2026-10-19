import Leanux.Proofs.WG.RetirementSecurity.ZeroTimerQueued

/-! The original recorded timer-dispatch unit carries a live selected peer
through timer detachment and enters its actual zero-key callback. Record and
bucket guards remain in the source and may stop. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ZeroTimerDispatch
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

def Live (pid : PeerId) (w : WGWorld) : Prop :=
  ((ConfiguredIdentity.view w).bind fun s=>(s.peers pid).map (·.dead))=some false

def Queued (pid : PeerId) (w : WGWorld) : Prop :=
  ∃d,w.dev=some d ∧ pid∈d.clearWorkQueue

theorem live_peer (entry : Live pid w) : ∃p,peerAt w pid=some p ∧ p.isDead=false := by
  unfold Live ConfiguredIdentity.view ConfiguredIdentity.state at entry
  cases device:w.dev with
  | none=>simp [device] at entry
  | some d=>
    cases stored:d.peers[pid]? with
    | none=>simp [device,stored] at entry
    | some p=>exact ⟨p,by simp [peerAt,device,stored],by simpa [device,stored,ConfiguredIdentity.cell] using entry⟩

theorem callback (pid : PeerId) : Hoare (expiredZeroKeyMaterial pid) (Live pid) (fun _=>Queued pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  cases result
  obtain ⟨p,found,alive⟩ := live_peer entry
  exact ZeroTimerQueued.callback pid p alive found a b run

def DeviceStable (P : WGWorld→Prop) : Prop :=
  ∀w v,v.dev=w.dev→P w→P v

theorem live_stable : DeviceStable (Live pid) := by
  intro w v same before
  simpa only [Live,ConfiguredIdentity.view,same] using before

theorem queued_stable : DeviceStable (Queued pid) := by
  rintro w v same ⟨d,device,member⟩
  exact ⟨d,same.trans device,member⟩

theorem stored (P : WGWorld→Prop) (stable : DeviceStable P)
    {action : Leanux.M α} (same : SameProductStore action) :
    Preserves (fun w : World=>P w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  have store := (ProjectedAction.iff_run _ _ _).mp same w result v run
  exact stable w.wg v.wg (congrArg (fun s : ProductStore43=>s.2.2.2.dev) store) entry

theorem ambient (P : WGWorld→Prop) (action : AmbientM α) :
    Preserves (fun w : World=>P w.wg) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ before=>before)

theorem worker (P Q : WGWorld→Prop) (kind : Worker) (body : Leanux.M Unit)
    (acts : Hoare body (fun w=>P w.wg) (fun _ w=>Q w.wg)) :
    Hoare (Env.runWorker kind body) (fun w=>P w.wg) (fun _ w=>Q w.wg) := by
  by_cases net : kind==.netRx
  all_goals simp (config:={zeta:=true}) only [Env.runWorker,net,ite_true,hidden,modifyAmbient]
  all_goals
    apply hoare_bind _ _ (ambient P (AmbientM.hidden (.sectionStart kind)))
    intro _
  · apply hoare_bind _ _ (ambient P _)
    intro _
    apply hoare_bind _ _ acts
    intro _
    apply preserves_bind (ambient Q _)
    intro _
    apply preserves_bind (ambient Q (AmbientM.hidden (.sectionStop kind)))
    intro _
    exact preserves_pure ()
  · apply hoare_bind _ _ acts
    intro _
    apply preserves_bind (ambient Q (AmbientM.hidden (.sectionStop kind)))
    intro _
    exact preserves_pure ()

theorem timer_section (pid : PeerId) (kind : Worker) :
    Hoare (Env.runTimerSection kind (liftWG (timerCallback pid .zeroKeyMaterial)))
      (fun w=>Live pid w.wg) (fun _ w=>Queued pid w.wg) := by
  unfold Env.runTimerSection
  split
  · apply (hoare_iff_run _ _ _).mpr
    intro w result v entry run
    change Except.error _=Except.ok _ at run
    cases run
  · apply hoare_bind _ _ (show Preserves (fun w : World=>Live pid w.wg)
        (modifyAmbient fun s=>{s with fired:=s.fired.push kind.symbol}) from by
      unfold modifyAmbient
      exact ambient (Live pid) _)
    intro _
    apply worker
    apply (hoare_iff_run _ _ _).mpr
    intro w result v entry run
    exact (hoare_iff_run_ambient _ _ _).mp (callback pid)
      w.wg w.ambient result v.wg v.ambient entry (HolderPoll.native_receipt run)

theorem detach (pid : PeerId) :
    Preserves (fun w : World=>Live pid w.wg) (liftWG (delTimer pid .zeroKeyMaterial)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp (ConfiguredIdentity.delTimer_view pid .zeroKeyMaterial)
    w.wg w.ambient result v.wg v.ambient (HolderPoll.native_receipt run)
  simpa only [Live,same] using entry

theorem step_complete (P : WGWorld→Prop) (stable : DeviceStable P) (bucket : UInt64) :
    Preserves (fun w : World=>P w.wg) (Env.requireStepComplete bucket) := by
  unfold Env.requireStepComplete
  apply preserves_bind (stored P stable (liftWG_sameProductStore getDev getDev_sameWGStore))
  intro d
  cases TimerWheel.anotherAtStep d bucket with
  | none=>exact preserves_pure _
  | some pair=>cases pair; exact hoare_throw _


theorem modify_device (P : WGWorld→Prop) (stable : DeviceStable P) (f : WGWorld→WGWorld)
    (same : ∀w,(f w).dev=w.dev) : Preserves (fun w : World=>P w.wg) (modifyWG f : Leanux.M Unit) := by
  unfold modifyWG
  apply hoare_modify
  intro w before
  exact stable w.wg (f w.wg) (same w.wg) before

theorem dispatch_tail (kind : Worker) (pid : PeerId) (entry : WheelEntry) :
    Hoare (do
      liftWG (delTimer pid .zeroKeyMaterial)
      modifyWG fun s=>{s with timerPassStep:=some entry.bucketExpiry}
      Env.runTimerSection kind (liftWG (timerCallback pid .zeroKeyMaterial))
      modifyWG fun s=>{s with timerPassStep:=none})
      (fun w=>Live pid w.wg) (fun _ w=>Queued pid w.wg) := by
  apply hoare_bind _ _ (detach pid)
  intro _
  apply hoare_bind _ _ (modify_device (Live pid) live_stable
    (fun s=>{s with timerPassStep:=some entry.bucketExpiry}) (fun _=>rfl))
  intro _
  apply hoare_bind _ _ (timer_section pid kind)
  intro _
  exact modify_device (Queued pid) queued_stable
    (fun s=>{s with timerPassStep:=none}) (fun _=>rfl)

open Lean Meta Elab Tactic in
private def dispatchAction (target : Expr) : TacticM (Array Expr × Nat) := do
  unless target.isAppOf ``Hoare do throwError "not a Hoare contract"
  let args := target.getAppArgs
  return (args,args.size-3)

open Lean Meta Elab Tactic in
elab "zero_dispatch_bind " n:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let (args,index) ← dispatchAction target
  let action := args[index]!.consumeMData
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let parts := action.getAppArgs
  let head := parts[parts.size-2]!.consumeMData
  let expected ← realizeGlobalConstNoOverloadWithInfo n
  unless head.isAppOf expected do throwError "different bound action"

open Lean Meta Elab Tactic in
elab "zero_dispatch_step" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let (args,index) ← dispatchAction target
  let action := args[index]!.consumeMData
  if let .letE _ _ value body _ := action then
    replaceMainGoal [← goal.replaceTargetDefEq (mkAppN target.getAppFn (args.set! index (body.instantiate1 value)))]
    return
  let reduced := action.headBeta
  if !Expr.equal action reduced then
    replaceMainGoal [← goal.replaceTargetDefEq (mkAppN target.getAppFn (args.set! index reduced))]
    return
  if action.isAppOf ``ite || action.isAppOf ``dite then
    evalTactic (← `(tactic| split))
  else if (← matchMatcherApp? action).isSome then
    replaceMainGoal (← Split.splitMatch goal action)
  else throwError "not a dispatch choice"

theorem stopped (stop : Stop) (tail : α→Leanux.M β) (P : World→Prop) (Q : β→World→Prop) :
    Hoare ((throw stop : Leanux.M α)>>=tail) P Q := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases run

/-- This is the actual recorded dispatch unit inside the original wheel loop,
including worker, timer-address and preceding-bucket checks. A normal unit
selected for a live peer's zero-key timer leaves that peer queued for clearing. -/
theorem dispatch (kind : Worker) (pid : PeerId) (entry : WheelEntry) (prior : Option UInt64) :
    Hoare (timerDispatchUnit kind pid .zeroKeyMaterial entry prior)
      (fun w=>Live pid w.wg) (fun _ w=>Queued pid w.wg) := by
  unfold timerDispatchUnit
  simp (config:={zeta:=false}) only [peekUnit]
  repeat' first
    | (zero_dispatch_bind liftM; exact dispatch_tail kind pid entry)
    | (zero_dispatch_bind Env.timerWorker
       apply hoare_bind _ _ (stored (Live pid) live_stable (timerWorker_sameKernel .zeroKeyMaterial))
       intro expected)
    | (zero_dispatch_bind MonadLiftT.monadLift
       apply hoare_bind _ _ (ambient (Live pid) (AmbientM.peekUnit kind))
       intro unit)
    | (zero_dispatch_bind getWG
       apply hoare_bind _ _ (stored (Live pid) live_stable
         (fun initial=>productGetWG_spec (fun s=>s=initial)))
       intro world)
    | (zero_dispatch_bind Env.requireStepComplete
       apply hoare_bind _ _ (step_complete (Live pid) live_stable _)
       intro ignored)
    | (zero_dispatch_bind throw; exact stopped _ _ _ _)
    | zero_dispatch_step

/-- Original dispatch preserves the initialized holder account, and a peer
with a published slot is live by the derived endpoint carrier. No incoming
account or liveness invariant is assumed. -/
theorem initialized_dispatch (trace : Runner.Trace) (placeholders : Bool)
    (initialized : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h))
    (kind : Worker) (pid : PeerId) (entry : WheelEntry) (prior : Option UInt64)
    (p : Peer) (found : peerAt w.wg pid=some p) (published : HasKeySlot p)
    (run : (timerDispatchUnit kind pid .zeroKeyMaterial entry prior).run w=.ok ((),v)) :
    HolderAccount [] v.wg ∧ Queued pid v.wg := by
  obtain ⟨carriers,whole⟩ := HolderInitialized.initialized trace placeholders initialized
  have ready : HolderTimerKeys.ProductReady [] [] [] w := ⟨whole.2,whole.1.1.2.2⟩
  have alive := whole.2.2.2.2 pid p found (by simp) published
  have live : Live pid w.wg := by
    unfold Live ConfiguredIdentity.view ConfiguredIdentity.state
    cases device:w.wg.dev with
    | none=>simp [peerAt,device] at found
    | some d=>
      have stored : d.peers[pid]?=some p := by simpa [peerAt,device] using found
      simp [stored,ConfiguredIdentity.cell,alive]
  exact ⟨((hoare_iff_run _ _ _).mp
    (HolderTimerKeys.dispatch (temporary:=[]) (locals:=[]) (active:=[]) kind pid .zeroKeyMaterial entry prior)
    w () v ready run).1.1,
    (hoare_iff_run _ _ _).mp (dispatch kind pid entry prior) w () v live run⟩

end Leanux.Proofs.WG.RetirementSecurity.ZeroTimerDispatch
