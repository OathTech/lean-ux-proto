import Leanux.Proofs.WG.AuthenticatedEffects.WorkRootFrames
import Leanux.Proofs.WG.AuthenticatedEffects.TimerRootProjection

/-! Projection of the complete receiver with actual deferred-work receipts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.WorkRoot
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources TimerRoot
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private theorem keepalive_projects (pid : PeerId) :
    Projects (TimerRoot.call .keepalive pid (fun origin => keepalive origin pid))
      (HandshakeCausal.call .keepalive pid (sendKeepalive pid)) :=
  call_projects _ _ _ _ (fun _ => keepalive_erases _ _) (fun _ => keepalive_frame _ _)

elab "work_root_project_choice" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``Projects do Lean.throwError "expected a projection"
  let args := target.getAppArgs
  unless args[args.size - 2]!.isAppOf ``ite do Lean.throwError "expected an explicit choice"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply projects_choice))

theorem responseWith_projects (mac : HandshakeMac) (pid : PeerId) :
    Projects (responseWith (ops mac) pid) (responseWith (HandshakeCausal.ops mac) pid) := by
  unfold responseWith
  simp only [ops,TimerRoot.ops,HandshakeCausal.ops]
  repeat' first
    | with_reducible exact old_call_projects _ _ _
    | with_reducible exact keepalive_projects _
    | with_reducible exact derived_projects _
    | with_reducible exact traversal_projects _
    | with_reducible exact projects_lift _
    | with_reducible exact projects_pure _
    | with_reducible apply projects_bind
    | split
    | work_root_project_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only [Option.some.injEq]

elab "work_root_response_projects" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``Projects do Lean.throwError "expected a projection"
  let args := target.getAppArgs
  unless args[args.size - 2]!.isAppOf ``responseWith do Lean.throwError "expected a response sender"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact responseWith_projects _ _))

theorem afterMac_projects (mac : HandshakeMac) (msg : Key) (src : SkbSource)
    (loaded : Bool) (state : MacState) :
    Projects (afterMacWith (ops mac) msg src loaded state)
      (afterMacWith (HandshakeCausal.ops mac) msg src loaded state) := by
  unfold afterMacWith
  simp only [ops,TimerRoot.ops,HandshakeCausal.ops]
  repeat' first
    | work_root_response_projects
    | with_reducible exact old_initiation_projects _
    | with_reducible exact old_response_projects _
    | with_reducible exact old_call_projects _ _ _
    | with_reducible exact keepalive_projects _
    | with_reducible exact derived_projects _
    | with_reducible exact traversal_projects _
    | with_reducible exact projects_lift _
    | with_reducible exact projects_pure _
    | with_reducible apply projects_bind
    | split
    | work_root_project_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only [Option.some.injEq]


theorem receive_projects (msg : Key) (src : SkbSource) :
    Projects (receive msg src) (HandshakeCausal.receive msg src) := by
  unfold receive HandshakeCausal.receive
  apply projects_bind _ _ _ _ (projects_lift _)
  intro cookie
  split
  · exact projects_bind _ _ _ _ (projects_lift _) (fun _ => projects_pure _)
  · apply projects_bind _ _ _ _ (projects_lift _)
    intro loaded
    apply projects_bind _ _ _ _ (capture_projects _)
    intro checked
    exact afterMac_projects _ _ _ _ _

theorem receive_erases (msg : Key) (src : SkbSource) :
    ErasesStatePrefix (receive msg src) (receiveHandshakePacket msg src) := by
  intro w ambient h
  exact (congrArg Prod.fst (receive_projects msg src w ambient h)).symm.trans
    (HandshakeCausal.receive_erases msg src w ambient (history h))

end Leanux.Proofs.WG.AuthenticatedEffects.WorkRoot
