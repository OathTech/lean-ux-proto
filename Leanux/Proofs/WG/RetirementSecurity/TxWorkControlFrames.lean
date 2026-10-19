import Leanux.Proofs.WG.RetirementSecurity.TxRunnerInitialSuspension

/-! Native routing and lifecycle frames for the service carrier retain actual
suspended actors as well as allocated TX ownership and pending work. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem actor_routing {action : Net.M α} (suspension : TxSuspension.Keeps action) :
    Preserves (At (Covered locals crypt) crypt active) (monadLift action : Leanux.M α) :=
  actor_product_store (fun initial=>productRouting_spec action (fun s=>s=initial))
    (TxSuspension.Fib.product_routing suspension)

theorem actor_get_routing : Preserves (At P crypt active) (getRouting : Leanux.M Net.Routing) := by
  apply at_frame
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  rfl

theorem actor_modify_routing (f : Net.Routing→Net.Routing) :
    Preserves (At (Covered locals crypt) crypt active) (modifyRouting f : Leanux.M Unit) :=
  actor_routing (TxSuspension.modify _)

theorem actor_cut (sites : List HiddenSite) :
    Preserves (At P crypt active) (skipCut sites : Leanux.M Unit) :=
  actor_ambient (TxSuspension.cut_ambient sites)

theorem actor_no_crypt : Preserves (At P crypt active) Env.requireNoCryptWork := by
  unfold Env.requireNoCryptWork
  repeat' actor_neutral_step

theorem actor_idle : Preserves (At P crypt active) Env.requireIdleDevice := by
  unfold Env.requireIdleDevice
  repeat' first
    | (rx_retention_head Env.requireNoCryptWork; exact actor_no_crypt)
    | actor_neutral_step

theorem serving_mtu (mtu : Int) : Preserves (Serving locals crypt tx) (WG.setMtu mtu) := by
  unfold WG.setMtu
  repeat' serving_metadata_step

theorem actor_mtu (mtu : Int) :
    Preserves (At (Covered locals crypt) crypt active) (liftWG (WG.setMtu mtu)) := by
  apply At.native (fun _=>serving_mtu mtu)
  suspension_source [WG.setMtu] using [TxSuspension.modify_device]

theorem serving_pre_exit : Preserves (Serving locals crypt tx) WG.netnsPreExit := by
  unfold WG.netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketReinit; exact serving_socket_reinit _ _)
    | (rx_retention_head clearPeerEndpointSrc; exact serving_clear_endpoint _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Serving locals crypt tx)
       intro item state
       change Preserves (Serving locals crypt tx) _)
    | (rx_retention_head get
       exact hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2))
    | serving_metadata_step

theorem actor_pre_exit :
    Preserves (At (Covered locals crypt) crypt active) (liftWG WG.netnsPreExit) := by
  apply At.native (fun _=>serving_pre_exit)
  suspension_source [WG.netnsPreExit] using
    [TxSuspension.branch,TxSuspension.device,TxSuspension.modify_device,
     TxSuspension.socket_reinit,TxSuspension.clear_endpoint]

theorem actor_sleep : Preserves (At (Covered locals crypt) crypt active) (liftWG mayHaveSlept) :=
  At.native (fun _=>serving_store mayHaveSlept_sameWGStore) TxSuspension.slept

macro "actor_control_step" : tactic => `(tactic| first
  | (rx_retention_head getRouting; exact actor_get_routing)
  | (rx_retention_head modifyRouting; exact actor_modify_routing _)
  | (rx_retention_head skipCut; exact actor_cut _)
  | (rx_retention_head Env.requireNoCryptWork; exact actor_no_crypt)
  | (rx_retention_head Env.requireIdleDevice; exact actor_idle)
  | (allocation_release_lift_from Net.M
     apply actor_routing
     first
     | env_operation_fact TxSuspension.Fib.cache_flush
     | env_operation_fact TxSuspension.Fib.netdev_up
     | env_operation_fact TxSuspension.Fib.netdev_down
     | env_operation_fact TxSuspension.Fib.netdev_unregister
     | env_operation_fact TxSuspension.Fib.netdev_mtu
     | env_operation_fact TxSuspension.Fib.addr_down
     | env_operation_fact TxSuspension.Fib.addr_up
     | env_operation_fact TxSuspension.Fib.table_insert
     | env_operation_fact TxSuspension.Fib.table_delete)
  | actor_neutral_step)

end Leanux.Proofs.WG.RetirementSecurity.TxWork
