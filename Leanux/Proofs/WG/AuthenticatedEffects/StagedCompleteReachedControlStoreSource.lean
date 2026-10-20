import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProductComponentSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchStoreSource

/-! Administrative calls that leave the packet store intact retain their
native routing adapters, descriptor wrappers, branches and failure results. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductStore
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

noncomputable def listShape (items : List ι) (initial : σ)
    (body : ι → σ → Leanux.M (ForInStep σ))
    (sources : ∀ item acc,Shape (body item acc)) : Shape (forIn items initial body) :=
  List.rec (motive:=fun values=>∀ acc,Shape (forIn values acc body))
    (fun acc=>.pure acc)
    (fun value rest ih acc=>(List.forIn_cons body value rest acc).symm ▸
      Shape.bind (sources value acc) (fun decision=>match decision with
        | .done final=>.pure final | .yield next=>ih next)) items initial

noncomputable def conditionalShape (test : Prop) [Decidable test]
    {yes no : Leanux.M α} (left : test → Shape yes) (right : ¬test → Shape no) :
    Shape (if test then yes else no) := by
  split
  · exact left ‹_›
  · exact right ‹_›

elab "control_store_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a product store source"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn | Lean.throwError "not a constant source"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("."++name) do
    Lean.throwError "different source head"

macro "control_store_step" : tactic => `(tactic| first
  | (control_store_head Pure.pure;exact Shape.pure _)
  | (control_store_head Bind.bind;apply Shape.bind)
  | (control_store_head ForIn.forIn;apply listShape)
  | (control_store_head ite;apply conditionalShape)
  | exact fsShape (getFiles : FS.M FilesStruct)
  | exact fsShape (monadLift (TaskM.getTask _) : FS.M Task)
  | exact taskShape (TaskM.getTask .task)
  | exact fsShape _
  | exact taskShape _
  | exact routeShape _
  | dispatch_store_step)

noncomputable def socketShape (fd : Nat) (source : Shape body) : Shape (Leanux.socketCallOn fd body) := by
  unfold Leanux.socketCallOn
  repeat' first | exact source | control_store_step

noncomputable def rtnetlinkShape (source : Shape body) : Shape (Leanux.rtnetlinkRequest body) := by
  unfold Leanux.rtnetlinkRequest
  repeat' first | exact source | (control_store_head socketCallOn;apply socketShape) | control_store_step

noncomputable def deladdrShape (family : Nat) : Shape (Env.wgDeladdr family) := by
  unfold Env.wgDeladdr
  repeat' control_store_step

noncomputable def delrouteShape (family : Nat) (named : Bool) (dst plen oif kind metric : Nat) :
    Shape (Env.wgDelroute family named dst plen oif kind metric) := by
  unfold Env.wgDelroute
  repeat' control_store_step

noncomputable def addrouteShape (dst plen oif kind metric mtu flags : Nat) :
    Shape (Env.wgAddroute dst plen oif kind metric mtu flags) := by
  unfold Env.wgAddroute
  repeat' control_store_step

noncomputable def addaddrShape (addr plen : Nat) : Shape (Env.wgAddaddr addr plen) := by
  unfold Env.wgAddaddr
  repeat' control_store_step

noncomputable def advanceShape (ticks : Nat) : Shape (Env.advance ticks) := by
  unfold Env.advance
  repeat' control_store_step

noncomputable def advanceCallShape (ticks : Nat) : Shape (Leanux.dispatch (.wgAdvance ticks)) := by
  unfold Leanux.dispatch
  repeat' first | exact advanceShape _ | control_store_step

noncomputable def netnsCloseShape : Shape Leanux.netnsClose := by
  unfold Leanux.netnsClose Env.pendingDevice
  repeat' control_store_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductStore
