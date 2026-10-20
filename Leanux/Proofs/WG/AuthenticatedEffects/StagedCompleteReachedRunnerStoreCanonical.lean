import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPrefixStoreFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReturnSource

/-! Canonical native runner entry and return metadata. These are source
trees of the existing helpers, including their original subsystem calls. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PrefixStore
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

noncomputable def listShape (items : List ι) (initial : σ)
    (body : ι → σ → PrefixM Event (ForInStep σ))
    (sources : ∀ item acc,Shape (body item acc)) : Shape (forIn items initial body) :=
  List.rec (motive:=fun values=>∀ acc,Shape (forIn values acc body))
    (fun acc=>.pure acc)
    (fun value rest ih acc=>(List.forIn_cons body value rest acc).symm ▸
      Shape.bind (sources value acc) (fun decision=>match decision with
        | .done final=>.pure final | .yield next=>ih next)) items initial

noncomputable def conditionalShape (test : Prop) [Decidable test]
    {yes no : PrefixM Event α} (left : test → Shape yes) (right : ¬test → Shape no) :
    Shape (if test then yes else no) := by
  split
  · exact left ‹_›
  · exact right ‹_›

elab "prefix_store_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a logged store source"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn | Lean.throwError "not a constant source"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("."++name) do
    Lean.throwError "different source head"

macro "prefix_store_step" : tactic => `(tactic| first
  | (prefix_store_head Pure.pure;exact Shape.pure _)
  | (prefix_store_head Bind.bind;apply Shape.bind)
  | (prefix_store_head ForIn.forIn;apply listShape)
  | (prefix_store_head ite;apply conditionalShape)
  | exact Shape.native (ProductStore.fsShape (StateT.lift TaskM.getCurrent))
  | exact Shape.native (ProductStore.fsShape _)
  | exact Shape.native (ProductStore.seccompShape _)
  | exact Shape.native (.reading ProductRead.routingShape)
  | exact Shape.native (.reading ProductRead.environmentShape)
  | exact Shape.native (.ambient (modify _))
  | exact Shape.native (.ambient (AmbientM.unsupported _))
  | exact Shape.native (.ambient AmbientM.skipAmbient)
  | exact Shape.native (.write _ (fun _=>rfl))
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

noncomputable def enterShape (call : Syscall) : Shape (SyscallSource.enter call) := by
  unfold SyscallSource.enter
  repeat' prefix_store_step

noncomputable def preludeShape : Shape ReturnSource.prelude := by
  unfold ReturnSource.prelude
  repeat' prefix_store_step

noncomputable def routingShape (call : Syscall) : Shape (ReturnSource.routing call) := by
  cases call <;> unfold ReturnSource.routing
  all_goals repeat' prefix_store_step

def skipShape : Shape (liftPrefix (skipAmbient : Leanux.M Unit)) :=
  .native (.ambient AmbientM.skipAmbient)

noncomputable def outsideShape (source : ProductStore.Shape body) :
    ProductStore.Shape (Env.outsideWindow body) := by
  unfold Env.outsideWindow
  repeat' first | exact source | control_store_step

noncomputable def routeNativeShape : ProductStore.Shape Env.routeIntoWg0 := by
  unfold Env.routeIntoWg0
  repeat' first
    | (control_store_head outsideWindow;apply outsideShape)
    | control_store_step

noncomputable def routeShape : Shape (liftPrefix Env.routeIntoWg0) := .native routeNativeShape

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PrefixStore
