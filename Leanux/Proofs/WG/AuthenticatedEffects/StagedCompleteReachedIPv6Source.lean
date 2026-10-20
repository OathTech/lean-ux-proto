import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiChildFree
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServicePointSource

/-! IPv6 receive has its literal predicate checks, excluded outcomes, WG
read and fixture inbox write. Its source has no nested packet callback. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.IPv6
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Napi.Points
abbrev History := List Event

abbrev NativeSource (action : Leanux.M α) :=
  {shape : Shape (liftPrefix action) // shape.ChildFree}

noncomputable def nativeSource (token : Native (liftPrefix action)) : NativeSource action :=
  ⟨.native token,True.intro⟩

noncomputable def bindSource {body : Leanux.M α} {next : α → Leanux.M β}
    (head : NativeSource body) (tail : ∀value,NativeSource (next value)) :
    NativeSource (body >>= next) := by
  change {shape : Shape (liftPrefix (body >>= next)) // shape.ChildFree}
  rw [Service.Points.lift_bind]
  exact ⟨.bind head.1 (fun value=>(tail value).1),head.2,fun value=>(tail value).2⟩

noncomputable def failedSource {body : Leanux.M α} (failure : Failure (liftPrefix body))
    (next : α → Leanux.M β) : NativeSource (body >>= next) := by
  change {shape : Shape (liftPrefix (body >>= next)) // shape.ChildFree}
  rw [Service.Points.lift_bind]
  exact ⟨.failed failure _,True.intro⟩

noncomputable def conditionalSource (test : Prop) [Decidable test]
    {left right : Leanux.M α} (yes : test → NativeSource left)
    (no : ¬test → NativeSource right) : NativeSource (if test then left else right) := by
  split
  · exact yes ‹_›
  · exact no ‹_›

elab "ipv6_source_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``NativeSource do Lean.throwError "not an IPv6 source"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn
    | Lean.throwError "not a constant source head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different source head"

noncomputable def sourceFree (bytes : List UInt8) : NativeSource (Leanux.Env.Stack.receive6 bytes) := by
  unfold Leanux.Env.Stack.receive6
  repeat' first
    | (ipv6_source_head ite; apply conditionalSource)
    | (ipv6_source_head Bind.bind; first
        | exact failedSource (.invariant _) _
        | exact failedSource (.excluded _) _
        | apply bindSource)
    | (ipv6_source_head getWG; exact nativeSource .world)
    | (ipv6_source_head modifyEnv; exact nativeSource (.inbox _))
    | intro value
    | (dsimp +failIfUnchanged only)

noncomputable def source (bytes : List UInt8) : Shape (liftPrefix (Leanux.Env.Stack.receive6 bytes)) :=
  (sourceFree bytes).1

theorem source_childFree (bytes : List UInt8) : (source bytes).ChildFree :=
  (sourceFree bytes).2

def Point (bytes : List UInt8) (w : World) (h : History) (u : World) (middle : History) : Prop :=
  ∃site,Napi.Points.Point Boundary (source bytes) w h site u middle

noncomputable def remainder (point : Point bytes w h u middle) : PrefixM Event Unit :=
  Classical.choose ((Classical.choose_spec point).childFree_remaining (source_childFree bytes))

theorem remainder_run (point : Point bytes w h u middle) :
    runPrefix (liftPrefix (Leanux.Env.Stack.receive6 bytes)) w h=runPrefix (remainder point) u middle :=
  Classical.choose_spec ((Classical.choose_spec point).childFree_remaining (source_childFree bytes))

/-- Every point in the fixed IPv6 source belongs to the child-free relation;
no nested packet callback can be omitted by choosing an empty interior. -/
theorem source_point (point : Napi.Points.Point inside (source bytes) w h site u middle) :
    Point bytes w h u middle :=
  ⟨site,point.childFree (source_childFree bytes)⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.IPv6
