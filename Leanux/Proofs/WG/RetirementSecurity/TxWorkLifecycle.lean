import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionLifecycle

/-! Original device up/down transports actual TX service. Device teardown's
no-residual claim is kept at its exact before-reset cut and has an explicit
empty suspended-actor boundary, rather than assuming cleanup drains actors. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem serving_open : Preserves (Serving locals crypt tx) wgOpen := by
  unfold wgOpen
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketInit; exact serving_socket_init _)
    | (rx_retention_head sendStagedPackets; exact serving_staged _)
    | (rx_retention_head sendKeepalive; exact serving_keepalive _)
    | serving_removal_step

theorem serving_up : Preserves (Serving locals crypt tx) wgUp := by
  unfold wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact serving_open)
    | serving_metadata_step

theorem serving_stop : Preserves (Serving locals crypt tx) wgStop := by
  unfold wgStop requireNotPending
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (rx_retention_head purgeStagedPackets; exact serving_purge _)
    | (rx_retention_head timersStop; exact serving_timers_stop _)
    | (rx_retention_head handshakeClear; exact serving_handshake_clear _)
    | (rx_retention_head resetLastSentHandshake; exact serving_reset _)
    | (rx_retention_head socketReinit; exact serving_socket_reinit _ _)
    | serving_removal_step

theorem serving_down : Preserves (Serving locals crypt tx) wgDown := by
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact serving_stop)
    | serving_metadata_step

theorem up_actor : Preserves (At (Covered locals crypt) crypt active) (liftWG wgUp) :=
  At.native (fun _=>serving_up) TxSuspension.up

theorem down_actor : Preserves (At (Covered locals crypt) crypt active) (liftWG wgDown) :=
  At.native (fun _=>serving_down) TxSuspension.down

theorem destruct_no_residual (before : At (Covered [] []) [] [] w)
    (idle : w.ambient.suspended=[])
    (run : (liftWG wgDestruct).run w=.ok ((),v)) :
    ∃u c,(Destruct.beforeReset.run w.wg).run w.ambient=.ok (((),u),c) ∧
      TxDisposition.txPackets u=(fun _=>none) ∧
      ((do _root_.modify fun g:WGWorld=>{g with dev:=none}; retireDeviceUnits : WG.M Unit).run u).run c=
        .ok (((),v.wg),v.ambient) :=
  Destruct.no_residual_reset (RunnerBoundary.at_idle before idle) (HolderPoll.native_receipt run)

end Leanux.Proofs.WG.RetirementSecurity.TxWork
