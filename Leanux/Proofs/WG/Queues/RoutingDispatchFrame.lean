import Leanux.Proofs.WG.Queues.JointSyscallLifecycle
import Leanux.Proofs.WG.Queues.JointHistorySource

/-! The explicitly non-mutating routing dispatch arms keep the entire routing
journal on every outcome. This is an observer property, not a state frame. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes AllowedIps

elab "joint_history_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless ty.isAppOf ``HistoryFrame do Lean.throwError "not a history frame"
  let args := ty.getAppArgs
  if args.isEmpty then Lean.throwError "missing observer"
  let action := args.back!.consumeMData
  let .const actual _ := action.getAppFn | Lean.throwError "not a constant action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different action"

macro "joint_history_step" : tactic => `(tactic| first
  | contradiction
  | source_history_join
  | source_history_join_use
  | source_history_reduce
  | (joint_history_head ite; apply HistoryFrame.ite)
  | (joint_history_head liftPrefix; exact HistoryFrame.lift _ _)
  | (joint_history_head Pure.pure; exact HistoryFrame.pure _ _)
  | (joint_history_head Bind.bind; apply HistoryFrame.bind)
  | (joint_history_head ForIn.forIn; apply HistoryFrame.forIn)
  | dsimp only
  | maintenance_intro
  | split)

theorem socketCallOnWith_frame {E F : Type} (ρ : E → Option F) (fd : Nat)
    {body : PrefixM E Int} (hb : HistoryFrame ρ body) :
    HistoryFrame ρ (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  unfold socketCallOnWith
  repeat' first | with_reducible exact hb | joint_history_step

theorem netlinkRequestWith_frame {E F : Type} (ρ : E → Option F)
    {body : PrefixM E Int} (hb : HistoryFrame ρ body) :
    HistoryFrame ρ (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold netlinkRequestWith
  repeat' first
    | with_reducible exact hb
    | (joint_history_head socketCallOnWith; apply socketCallOnWith_frame)
    | joint_history_step

theorem rtnetlinkRequestWith_frame {E F : Type} (ρ : E → Option F)
    {body : PrefixM E Int} (hb : HistoryFrame ρ body) :
    HistoryFrame ρ (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold rtnetlinkRequestWith
  repeat' first
    | with_reducible exact hb
    | (joint_history_head socketCallOnWith; apply socketCallOnWith_frame)
    | joint_history_step

/-- Set and delete are handled by their completed-mutation observers. The other
source arms emit no routing completion, even when they return errno or Stop. -/
theorem dispatchObserved_frame (call : Syscall)
    (hset : ∀ attrs, call ≠ .wgSet attrs) (hdelete : call ≠ .wgDelete) :
    HistoryFrame (fun e : RoutingCompletion => some e) (dispatchObserved call) := by
  cases call
  case wgSet attrs => exact False.elim (hset attrs rfl)
  case wgDelete => exact False.elim (hdelete rfl)
  all_goals unfold dispatchObserved
  all_goals repeat' first
    | (joint_history_head socketCallOnObserved
       rw [socketCallOnObserved_factor]
       apply socketCallOnWith_frame)
    | (joint_history_head netlinkRequestObserved
       rw [netlinkRequestObserved_factor]
       apply netlinkRequestWith_frame)
    | (joint_history_head rtnetlinkRequestObserved
       rw [rtnetlinkRequestObserved_factor]
       apply rtnetlinkRequestWith_frame)
    | (joint_history_head netnsCloseObserved; unfold netnsCloseObserved)
    | joint_history_step

/-- A whole-journal frame plus exact erasure gives equality with the raw lift;
no validity, reachability or history-independence hypothesis is used. -/
theorem frame_erases_eq_lift {E α : Type} {g : PrefixM E α} {source : Leanux.M α}
    (hh : HistoryFrame (fun e => some e) g) (he : ErasesPrefix g source) :
    g = liftPrefix source := by
  funext w
  apply ExceptT.ext
  funext h
  apply Prod.ext
  · exact he w h
  · change (runPrefix g w h).2 = h
    simpa only [List.filterMap_some] using hh w h

theorem dispatchObserved_eq_lift (call : Syscall)
    (hset : ∀ attrs, call ≠ .wgSet attrs) (hdelete : call ≠ .wgDelete) :
    dispatchObserved call = liftPrefix (Leanux.dispatch call) :=
  frame_erases_eq_lift (dispatchObserved_frame call hset hdelete) (dispatchObserved_erases call)

end Leanux.Proofs.WG.Configuration
