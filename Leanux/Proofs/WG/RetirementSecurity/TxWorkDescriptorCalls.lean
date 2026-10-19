import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionDescriptors

/-! Socket/netlink wrappers retain the actual native TX service carrier,
including suspended workers when their callback returns. No frame for an
arbitrary file or ambient computation is assumed. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.Proofs.Framing Lifetimes Queues

theorem actor_files {action : FS.M α} (suspension : TxSuspension.Nested.Keeps action) :
    Preserves (At (Covered locals crypt) crypt active) (liftFS action) :=
  At.product (fun _=>productFS_spec action _ (fun _ _ _ _ before=>before))
    (TxSuspension.Nested.product_fs suspension)

theorem actor_task_via_fs {action : TaskM α} (suspension : TxSuspension.Keeps action) :
    Preserves (At (Covered locals crypt) crypt active) (liftFS (StateT.lift action)) :=
  actor_files (TxSuspension.Nested.lift suspension)

open Lean Meta Elab Tactic in
elab "tx_file_lift " carrier:ident : tactic => withMainContext do
  evalTactic (← `(tactic| allocation_release_lift_from $carrier))
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let some action := target.getAppArgs.back? | throwError "missing action"
  let some source := action.consumeMData.headBeta.getAppArgs.back? | throwError "missing lifted source"
  let sourceSyntax ← Lean.Elab.Term.exprToSyntax source
  let name ← realizeGlobalConstNoOverloadWithInfo carrier
  if name == ``FS.M then
    evalTactic (← `(tactic| apply actor_files (action := $sourceSyntax)))
  else if name == ``TaskM then
    evalTactic (← `(tactic| apply actor_task_via_fs (action := $sourceSyntax)))
  else throwError "not a file/task lift"

theorem socket_actor (fd : Nat) (body : Leanux.M Int)
    (keeps : Preserves (At (Covered locals crypt) crypt active) body) :
    Preserves (At (Covered locals crypt) crypt active) (socketCallOn fd body) := by
  unfold socketCallOn
  apply preserves_bind (actor_files (TxSuspension.Nested.fd_get fd))
  intro f
  split
  · exact preserves_pure _
  · exact preserves_bind keeps (fun result=>
      preserves_bind (actor_files (TxSuspension.Nested.fd_put f)) (fun _=>preserves_pure result))

theorem netlink_actor (body : Leanux.M Int)
    (keeps : Preserves (At (Covered locals crypt) crypt active) body) :
    Preserves (At (Covered locals crypt) crypt active) (netlinkRequest body) := by
  unfold netlinkRequest socketCall
  repeat' first
    | exact keeps
    | (rx_retention_head socketCallOn; apply socket_actor)
    | actor_control_step

theorem rtnetlink_actor (body : Leanux.M Int)
    (keeps : Preserves (At (Covered locals crypt) crypt active) body) :
    Preserves (At (Covered locals crypt) crypt active) (rtnetlinkRequest body) := by
  unfold rtnetlinkRequest getFiles getTask modifyFiles modifyTask
  repeat' first
    | exact keeps
    | (rx_retention_head socketCallOn; apply socket_actor)
    | (tx_file_lift FS.M
       first
       | env_operation_fact TxSuspension.Nested.set_file
       | env_operation_fact TxSuspension.Nested.free_file
       | env_operation_fact TxSuspension.Nested.set_fd_slot
       | env_operation_fact TxSuspension.Nested.set_fd_open
       | env_operation_fact TxSuspension.Nested.set_fd_cloexec)
    | (tx_file_lift TaskM
       first
       | env_operation_fact TxSuspension.Nested.task_read
       | env_operation_fact TxSuspension.Nested.task_write)
    | (rx_retention_head get
       exact hoare_consequence (hoare_get _) (fun _ before=>before) (fun _ _ before=>before.2))
    | (rx_retention_head _root_.modify
       apply hoare_modify
       intro w before
       exact before.store rfl rfl)
    | actor_control_step


end Leanux.Proofs.WG.RetirementSecurity.TxWork
