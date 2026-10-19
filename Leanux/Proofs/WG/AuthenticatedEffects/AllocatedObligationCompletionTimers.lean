import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionKeyRelease
import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendLifetime

/-! The actual traversal and data-sent callbacks preserve selected packet
ownership. Their real arm receipts are retained, including before Stop;
neither callback settles a fixed packet obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CompletionCuts

private abbrev timerOps := LifetimeEffects.decorate
  (CompletionEffects.lifetimeBase (CausalJournal.Event.old ∘ Journal.completionEvent)
    CausalJournal.completion?) CausalJournal.scope? CausalJournal.Event.armed CausalJournal.Event.queued

private theorem decorated_appends (base : LifetimeEffects.Ops (WGPrefix E))
    (keeps : LifetimeEffects.Ops.Appends base)
    (scope : E → Option (CausalScope.Event Cause))
    (arm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (queue : TimerEffects.Queued (CausalEffects.Context Cause) → E) :
    LifetimeEffects.Ops.Appends (LifetimeEffects.decorate base scope arm queue) where
  step := keeps.step
  peer := keeps.peer
  keypair := keeps.keypair
  modifyPeer := keeps.modifyPeer
  guard := keeps.guard
  get := keeps.get
  put := keeps.put
  arm := fun pid timer delay caller w a h =>
    (keeps.arm pid timer delay caller).receiptWGObserved
      (fun r => arm ⟨CausalScope.current scope h,pid,timer,delay,caller,r⟩) w a h
  append := fun pid w a h => (keeps.append pid).receiptWGObserved
    (fun r => queue ⟨CausalScope.current scope h,pid,r⟩) w a h

private theorem base_appends : LifetimeEffects.Ops.Appends
    (CompletionEffects.lifetimeBase (CausalJournal.Event.old ∘ Journal.completionEvent)
      CausalJournal.completion?) := by
  constructor
  all_goals intros
  all_goals exact StateAppends.focus _ _ _

private theorem timer_appends : LifetimeEffects.Ops.Appends timerOps :=
  decorated_appends _ base_appends _ _ _

private theorem timer_projects : LifetimeEffects.Ops.Projects ledgerEvent? timerOps
    RawAppend.lifetimeLifted :=
  LifetimeEffects.decorate_projects ledgerEvent? _ _
    (RawAppend.lifetime_base_projects ledgerEvent? _ _ (fun _ => rfl))
    _ _ _ (fun _ => rfl) (fun _ => rfl)

macro "completion_timer_append" : tactic => `(tactic| first
  | with_reducible exact LifetimeEffects.Ops.Appends.step timer_appends _
  | with_reducible exact LifetimeEffects.Ops.Appends.peer timer_appends _
  | with_reducible exact LifetimeEffects.Ops.Appends.guard timer_appends _
  | with_reducible exact LifetimeEffects.Ops.Appends.arm timer_appends _ _ _ _
  | exact StateAppends.pure _
  | apply StateAppends.bind
  | (maintenance_intro; try dsimp only)
  | maintenance_reduce
  | split)

private theorem modify_appends (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateAppends (LifetimeEffects.modifyWith timerOps site pid timer delay) := by
  unfold LifetimeEffects.modifyWith
  repeat' completion_timer_append

theorem traversal_appends (pid : PeerId) : Appends (CausalJournal.completionOps.traversal pid) := by
  apply StateAppends.liftWGObserver
  change StateAppends (LifetimeEffects.traversalWith timerOps pid)
  unfold LifetimeEffects.traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | with_reducible exact modify_appends _ _ _ _
    | completion_timer_append

theorem dataSent_appends (pid : PeerId) : Appends (CausalJournal.completionOps.dataSent pid) := by
  apply StateAppends.liftWGObserver
  change StateAppends (LifetimeEffects.dataSentWith timerOps pid)
  unfold LifetimeEffects.dataSentWith
  repeat' completion_timer_append

theorem projected_native_checked (site : Site) (source : site.action = action)
    (appends : Appends action)
    (projected : ProjectsPrefix ledgerEvent? id action (liftPrefix (liftWG native)))
    (normal : ∀ w history value v, State context phase history w →
      (liftWG native).run w = .ok (value,v) → State context phase history v) :
    Holds context phase action := by
  apply quiet_native_checked site source appends
  · intro w h
    exact (congrArg Prod.snd (projected w h)).symm
  · intro w h
    have same := congrArg Prod.fst (projected w h)
    have eta : (fun x : Unit × World => (id x.1,x.2)) = id := by funext x; rfl
    simpa only [runPrefix_lift,eta,Except.map_id,id_eq] using same.symm
  · exact normal

theorem traversal_checked (context : Context) (phase : Phase) :
    Holds context phase (CausalJournal.completionOps.traversal context.pid) := by
  apply projected_native_checked (native := timersTraversal context.pid)
    (.traversal context.pid) rfl (traversal_appends context.pid)
  · change ProjectsPrefix ledgerEvent? id
      (liftWGObserver (LifetimeEffects.traversalWith timerOps context.pid))
      (liftPrefix (liftWG (timersTraversal context.pid)))
    have projected := (LifetimeEffects.traversal_projects ledgerEvent? timer_projects context.pid).liftWGObserver ledgerEvent? id
    simpa only [RawAppend.lifetime_traversal,liftWGObserver_lift] using projected
  · intro w h value v before run
    exact before.native _ (PacketOrigins.snapshot_wire (timersTraversal_cryptWire context.pid))
      (timersTraversal_ownership context.pid) run

theorem dataSent_checked (context : Context) (phase : Phase) :
    Holds context phase (CausalJournal.completionOps.dataSent context.pid) := by
  apply projected_native_checked (native := timersDataSent context.pid)
    (.dataSent context.pid) rfl (dataSent_appends context.pid)
  · change ProjectsPrefix ledgerEvent? id
      (liftWGObserver (LifetimeEffects.dataSentWith timerOps context.pid))
      (liftPrefix (liftWG (timersDataSent context.pid)))
    have projected := (LifetimeEffects.dataSent_projects ledgerEvent? timer_projects context.pid).liftWGObserver ledgerEvent? id
    simpa only [RawAppend.lifetime_dataSent,liftWGObserver_lift] using projected
  · intro w h value v before run
    exact before.native _ (PacketOrigins.snapshot_wire (timersDataSent_cryptWire context.pid))
      (timersDataSent_ownership context.pid) run

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
