import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTimerFrames

/-! The actual timer-modification source retains the full fixed-ledger entry
at its native clock/guard and arm cuts. A stopped arm keeps its reached entry
even though the native StateT does not return a final world on failure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.TimerSource
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity

def decisionPrefix (site : HiddenSite) (pid : PeerId) : WG.M (Option (Option UInt64)) := do
  let clock ← callerJiffies site
  if ← modPeerTimerGuard pid then return some clock
  return none

def suffix (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Option (Option UInt64) → WGPrefix CausalJournal.Event Bool
  | none => pure false
  | some clock => do
    CausalJournal.effects.arm pid timer delay clock
    pure true

theorem factor (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    TimerEffects.modifyWith CausalJournal.effects site pid timer delay =
      (liftWGPrefix (decisionPrefix site pid) >>= suffix pid timer delay) := by
  unfold TimerEffects.modifyWith decisionPrefix
  simp only [CausalJournal.effects,CausalEffects.ops,TimerEffects.observed,
    Queued.lift_bind,bind_assoc,Queued.lift_if]
  apply Queued.bind_same
  intro clock
  apply Queued.bind_same
  intro ready
  cases ready <;> simp only [Bool.false_eq_true,↓reduceIte,Queued.lift_pure,pure_bind,suffix]
  rfl

theorem prefix_frame (site : HiddenSite) (pid : PeerId) :
    SameView StagedEntry.view (decisionPrefix site pid) := by
  unfold decisionPrefix
  apply SameView.bind ((callerJiffies_sameWGWorld site).factor StagedEntry.view)
  intro clock
  apply SameView.bind (TimerFrames.guard pid)
  intro ready
  split <;> exact SameView.pure _ _

theorem run (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (w : WGWorld) (a : Ambient) (h : List CausalJournal.Event) :
    runWGPrefix (TimerEffects.modifyWith CausalJournal.effects site pid timer delay) w a h =
      match ((decisionPrefix site pid).run w).run a with
      | .error stop => (.error stop,h)
      | .ok ((ready,v),b) => runWGPrefix (suffix pid timer delay ready) v b h := by
  rw [factor]
  simp only [runWGPrefix,runStatePrefix_bind,liftWGPrefix,runStatePrefix_lift]
  cases ((decisionPrefix site pid).run w).run a <;> rfl

def receipt (pid : PeerId) (timer : PeerTimer) (delay : Nat) (clock : Option UInt64)
    (w v : WGWorld) (a b : Ambient) (h : List CausalJournal.Event) :
    TimerEffects.Arm CausalJournal.Context :=
  ⟨CausalScope.current CausalJournal.scope? h,pid,timer,delay,clock,⟨(),w,v,a,b⟩⟩

theorem arm_run (pid : PeerId) (timer : PeerTimer) (delay : Nat) (clock : Option UInt64)
    (w : WGWorld) (a : Ambient) (h : List CausalJournal.Event) :
    runWGPrefix (CausalJournal.effects.arm pid timer delay clock) w a h =
      match ((armTimer pid timer delay clock).run w).run a with
      | .error stop => (.error stop,h)
      | .ok ((_,v),b) => (.ok (((),v),b),h ++ [.armed (receipt pid timer delay clock w v a b h)]) := by
  change runWGPrefix (TimerEffects.armReceipt CausalJournal.Event.armed
    (CausalScope.current CausalJournal.scope? h) pid timer delay clock) w a h = _
  rw [TimerEffects.armReceipt,runWGPrefix_receiptWGObserved,runWGPrefix_lift]
  cases result : ((armTimer pid timer delay clock).run w).run a with
  | error stop => rfl
  | ok out => obtain ⟨⟨ignored,v⟩,b⟩ := out; cases ignored; rfl

theorem arm_entry (before : Inv h ledger debts locals w) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (clock : Option UInt64) (a b : Ambient)
    (native : ((armTimer pid timer delay clock).run w).run a = .ok (((),v),b)) :
    Inv (h ++ [.armed (receipt pid timer delay clock w v a b h)]) ledger debts locals v := by
  have after := before.same_view ((ProjectedAction.iff_run_ambient _ _ _).mp
    (TimerFrames.arm pid timer delay clock) w a () v b native)
  exact Queued.Inv.history after [_]
    (by intro event member; simp only [List.mem_singleton] at member; subst event; rfl)

inductive NormalTrace (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (w : WGWorld) (a : Ambient) (h : List CausalJournal.Event) :
    Bool → WGWorld → Ambient → List CausalJournal.Event → Prop
  | refused (native : ((decisionPrefix site pid).run w).run a = .ok ((none,v),b)) :
      NormalTrace site pid timer delay w a h false v b h
  | armed (ready : ((decisionPrefix site pid).run w).run a = .ok ((some clock,u),c))
      (native : ((armTimer pid timer delay clock).run u).run c = .ok (((),v),b)) :
      NormalTrace site pid timer delay w a h true v b
        (h ++ [.armed (receipt pid timer delay clock u v c b h)])

def StoppedCut (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (w : WGWorld) (a : Ambient) (h : List CausalJournal.Event)
    (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (stop : Stop) : Prop :=
  (((decisionPrefix site pid).run w).run a = .error stop ∧ Inv h ledger debts locals w) ∨
    ∃ clock u c, ((decisionPrefix site pid).run w).run a = .ok ((some clock,u),c) ∧
      ((armTimer pid timer delay clock).run u).run c = .error stop ∧ Inv h ledger debts locals u

def Result (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (w : WGWorld) (a : Ambient) (h : List CausalJournal.Event)
    (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (result : Except Stop ((Bool × WGWorld) × Ambient) × List CausalJournal.Event) : Prop :=
  match result.1 with
  | .error stop => result.2 = h ∧ StoppedCut site pid timer delay w a h ledger debts locals stop
  | .ok ((ready,v),b) => Inv result.2 ledger debts locals v ∧
      NormalTrace site pid timer delay w a h ready v b result.2

/-- The real timer guard and arm preserve every indexed obligation. Normal
success has its actual arm receipt; refusal has no receipt. Stop retains the
exact native failure and its reached full entry, never an unconstrained postcondition. -/
theorem checked (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (before : Inv h ledger debts locals w) (a : Ambient) :
    Result site pid timer delay w a h ledger debts locals
      (runWGPrefix (TimerEffects.modifyWith CausalJournal.effects site pid timer delay) w a h) := by
  rw [run]
  cases first : ((decisionPrefix site pid).run w).run a with
  | error stop => exact ⟨rfl,Or.inl ⟨first,before⟩⟩
  | ok out =>
    obtain ⟨⟨ready,u⟩,c⟩ := out
    have entry := before.same_view ((ProjectedAction.iff_run_ambient _ _ _).mp
      (prefix_frame site pid) w a ready u c first)
    cases ready with
    | none => exact ⟨entry,.refused first⟩
    | some clock =>
      change Result site pid timer delay w a h ledger debts locals
        (runWGPrefix (CausalJournal.effects.arm pid timer delay clock >>= fun _ => pure true) u c h)
      rw [runWGPrefix,runStatePrefix_bind]
      simp only [runStatePrefix_pure]
      have observed := arm_run pid timer delay clock u c h
      change runStatePrefix (CausalJournal.effects.arm pid timer delay clock) u c h = _ at observed
      rw [observed]
      cases armed : ((armTimer pid timer delay clock).run u).run c with
      | error stop => exact ⟨rfl,Or.inr ⟨clock,u,c,first,armed,entry⟩⟩
      | ok out =>
        obtain ⟨⟨ignored,v⟩,b⟩ := out
        cases ignored
        exact ⟨arm_entry entry pid timer delay clock c b armed,.armed first armed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.TimerSource
