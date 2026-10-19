import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedKeyAccessSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointResidual

/-! Key-reference and index mutations preserve the packet ownership view
at each fixed access cut. All frame premises follow from this source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.KeyAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity CausalJournal
open Prepare.Points
set_option maxHeartbeats 600000

theorem erase_framed (id stamp : Nat) (h : List LifetimeEvent) :
    Framed (eraseShape id stamp) w a h := by
  unfold eraseShape
  prepare_framed_uncast
  trivial

theorem remove_framed (id : KeypairId) (h : List LifetimeEvent) :
    Framed (removeShape id) w a h :=
  ⟨peerDeref_framed id h,fun _ _ _ _ _=>True.intro⟩

elab "key_access_frame_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Framed do Lean.throwError "not an access frame"
  let args := target.getAppArgs
  let some shape := args[args.size - 4]? | Lean.throwError "missing source witness"
  let .const actual _ := shape.consumeMData.headBeta.getAppFn | Lean.throwError "not a named source witness"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different source witness"

theorem canonical_framed (kid : Option KeypairId) (now : Bool) (h : List LifetimeEvent) :
    Framed (canonical kid now) w a h := by
  cases kid <;> cases now
  all_goals
    unfold canonical
    repeat' first
      | (key_access_frame_head removeShape; exact remove_framed _ _)
      | (key_access_frame_head eraseShape; exact erase_framed _ _ _)
      | prepare_direct_frame_step

/-- Every native observed key repayment cut preserves packet ownership,
including key removal before its original lifetime receipt. -/
theorem point_view
    (point : Point (canonical kid now) w a h site v b middle remaining) :
    StagedEntry.view v=StagedEntry.view w := point.view (canonical_framed kid now h)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.KeyAccess
