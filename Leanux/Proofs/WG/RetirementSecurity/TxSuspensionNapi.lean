import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionStack

/-! The original NAPI dispatch/section code preserves suspended activations.
Its RX poll contract is discharged by the actual GRO and stack source proof. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem product_modify_ambient (f : Ambient→Ambient) (same : ∀a,(f a).suspended=a.suspended) :
    SameView suspended (modifyAmbient f : Leanux.M Unit) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  exact same w.ambient

theorem product_get_ambient : SameView suspended (getAmbient : Leanux.M Ambient) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  rfl

theorem product_get_env : SameView suspended (getEnv : Leanux.M EnvWorld) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  rfl

theorem run_worker (worker : Worker) (body : Leanux.M Unit) (frame : SameView suspended body) :
    SameView suspended (Env.runWorker worker body) := by
  intro initial
  let P:=fun w=>suspended w=initial
  have hidden (site : HiddenSite) : Preserves P (Leanux.hidden site : Leanux.M (List UInt8)) :=
    product_ambient (TxActorFrames.hidden site) initial
  have write (f : Ambient→Ambient) (same : ∀a,(f a).suspended=a.suspended) :
      Preserves P (modifyAmbient f : Leanux.M Unit) := product_modify_ambient f same initial
  have call:Preserves P body := frame initial
  change Preserves P _
  unfold Env.runWorker
  repeat' first
    | env_operation_fact hidden
    | exact call
    | (rx_retention_head modifyAmbient; apply write; intro a; rfl)
    | routing_tx_step

theorem napi_softirq : SameView suspended Env.napiSoftirq := by
  intro initial
  let P:=fun w=>suspended w=initial
  have read:Preserves P (monadLift getDev : Leanux.M Device) := product device initial
  have ambient:Preserves P (getAmbient : Leanux.M Ambient) := product_get_ambient initial
  have peek:Preserves P (peekHiddenSite : Leanux.M (Option Nat)) := product_ambient TxActorFrames.peek_site initial
  have stopped {α : Type} (why : String) : Preserves P (Leanux.unsupported why : Leanux.M α) :=
    product_unsupported why initial
  have poll (pid budget : Nat) : Preserves P (rxPoll pid budget (fun packets=>packets.forM Env.deliverInner)) :=
    stack_poll pid budget initial
  have worker (w : Worker) (body : Leanux.M Unit) (frame : SameView suspended body) : Preserves P (Env.runWorker w body) :=
    run_worker w body frame initial
  change Preserves P _
  unfold Env.napiSoftirq
  repeat' first
    | env_operation_fact read
    | env_operation_fact ambient
    | env_operation_fact peek
    | env_operation_fact stopped
    | env_operation_fact poll
    | (rx_retention_head Env.runWorker
       apply worker
       intro inner
       change Preserves (fun w=>suspended w=inner) _
       have each (pid budget : Nat) : Preserves (fun w=>suspended w=inner)
           (rxPoll pid budget (fun packets=>packets.forM Env.deliverInner)) := stack_poll pid budget inner
       routing_tx_source [] using [each])
    | routing_tx_step

theorem napi_irq_exit : SameView suspended Env.napiIrqExit := by
  intro initial
  let P:=fun w=>suspended w=initial
  have read:Preserves P (monadLift getDev : Leanux.M Device) := product device initial
  have ambient:Preserves P (getAmbient : Leanux.M Ambient) := product_get_ambient initial
  have environment:Preserves P (getEnv : Leanux.M EnvWorld) := product_get_env initial
  have peek:Preserves P (peekHiddenSite : Leanux.M (Option Nat)) := product_ambient TxActorFrames.peek_site initial
  have write (f : EnvWorld→EnvWorld) : Preserves P (modifyEnv f) := environment_modify f initial
  have poll:Preserves P Env.napiSoftirq := napi_softirq initial
  change Preserves P _
  routing_tx_source [Env.napiIrqExit] using [read,ambient,environment,peek,write,poll]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
