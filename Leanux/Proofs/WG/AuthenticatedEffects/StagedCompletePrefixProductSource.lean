import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixProductFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityInitialized

/-! Outer file and netlink wrappers carry all logical journal prefixes through
the actual body. Native-only leaves reuse their established store frames. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

open Lean Meta Elab Tactic in
elab "prefix_product_native " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Checked do throwError "not a paired accounting product contract"
  let some action := target.getAppArgs.back? | throwError "missing action"
  let action := action.consumeMData.headBeta
  unless action.isAppOf ``liftPrefix do throwError "not a native product lift"
  let some native := action.getAppArgs.back? | throwError "missing native action"
  let native := native.consumeMData.headBeta
  let .const actual _ := native.getAppFn | throwError "not a constant native action"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different native head"

open Lean Meta Elab Tactic in
elab "prefix_product_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Checked do throwError "not a paired accounting product contract"
  let some action := target.getAppArgs.back? | throwError "missing action"
  let action := action.consumeMData.headBeta
  let action ← if action.isAppOf ``liftWGObserver then
      match action.getAppArgs.back? with
      | some body => pure body.consumeMData
      | none => throwError "missing WireGuard observer body"
    else pure action
  let .const actual _ := action.getAppFn | throwError "not a constant-headed source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different source head"

macro "prefix_product_step" : tactic => `(tactic| first
  | (prefix_product_head Pure.pure; exact pure_checked _)
  | (prefix_product_head Bind.bind; apply bind_checked)
  | (prefix_product_head ite; apply conditional)
  | (prefix_product_head ForIn.forIn; apply list)
  | (prefix_product_head captureObserved; apply capture)
  | maintenance_intro
  | (split; all_goals try simp_all only []; all_goals try subst_vars)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])


theorem read_files : Checked (liftPrefix (getFiles : Leanux.M FilesStruct)) :=
  native _ CompleteProduct.read_files

theorem read_task (t : TaskRef) : Checked (liftPrefix (getTask t : Leanux.M Task)) :=
  native _ (CompleteProduct.read_task t)

theorem modify_files (f : FilesStruct→FilesStruct) :
    Checked (liftPrefix (modifyFiles f : Leanux.M Unit)) :=
  native _ (CompleteProduct.modify_files f)

macro "prefix_outer_step" : tactic => `(tactic| first
  | (prefix_product_native liftSeccomp; exact seccomp _)
  | (prefix_product_native liftFS; exact fs _)
  | (prefix_product_native liftTask; exact task _)
  | (prefix_product_native get; exact read)
  | (prefix_product_native getFiles; exact read_files)
  | (prefix_product_native getTask; exact read_task _)
  | (prefix_product_native modifyFiles; exact modify_files _)
  | (prefix_product_native modify; apply edit; intro w; rfl)
  | (prefix_product_native skipCut; exact ambient _)
  | (prefix_product_native unsupported; exact ambient _)
  | (prefix_product_native invariant; exact ambient _)
  | (prefix_product_head liftPrefix; first | exact seccomp _ | exact fs _ | exact task _)
  | prefix_product_step)

theorem socket (fd : Nat) (body : PrefixM Event Int) (checked : Checked body) :
    Checked (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  unfold socketCallOnWith
  apply bind_checked (fs (fdget fd))
  intro f
  apply conditional
  · intro _; exact pure_checked _
  · intro _
    exact bind_checked checked (fun ret => bind_checked (fs (fdput f)) (fun _ => pure_checked ret))

theorem netlink (body : PrefixM Event Int) (checked : Checked body) :
    Checked (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold netlinkRequestWith
  apply bind_checked (socket _ _ (bind_checked (ambient (AmbientM.skipCut allocCuts))
    (fun _ => bind_checked checked (fun ret => bind_checked (ambient (AmbientM.skipCut allocCuts))
      (fun _ => pure_checked ret)))))
  intro ret
  exact bind_checked (socket _ _ (pure_checked 0)) (fun _ => pure_checked ret)

theorem rtnetlink (body : PrefixM Event Int) (checked : Checked body) :
    Checked (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold rtnetlinkRequestWith
  repeat' first
    | exact checked
    | (prefix_product_head socketCallOnWith; apply socket; change Checked _)
    | prefix_outer_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
