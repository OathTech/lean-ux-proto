import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionIngress

/-! Actual fixture packet construction, routing and inline receive service.
The native source controls suspended activations; the traffic family does not
assume all ambient actions leave them unchanged. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem pending_guard_actor (pid : PeerId) (why : String) :
    Preserves (At (Covered locals crypt) crypt active) (liftWG (requireNotPending pid why)) := by
  apply At.native
  · intro tx
    exact preserves_pure ()
  suspension_source [requireNotPending] using [TxSuspension.peer,TxSuspension.branch,TxSuspension.unsupported]

theorem fixture_send_actor : Preserves (At P crypt active) Env.fixtureSend := actor_cut _

theorem sender_source_actor (family dest tos : Nat) (ll : Bool) :
    Preserves (At (Covered locals crypt) crypt active) (Env.senderSource family dest tos ll) := by
  unfold Env.senderSource
  repeat' actor_control_step

theorem transmit_actor (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (At (Covered locals crypt) crypt active) (liftWG (wgXmit family addr packets mtu)) :=
  At.product (fun _=>serving_transmit family addr packets mtu)
    (TxSuspension.product (TxSuspension.transmit family addr packets mtu))

theorem multicast_actor (family addr : Nat) :
    Preserves (At (Covered locals crypt) crypt active) (Env.xmitMulticastLoop family addr) := by
  unfold Env.xmitMulticastLoop
  repeat' first
    | (allocation_release_lift_from WG.M
       exact At.native (fun _=>serving_store (Queues.loopbackSend_kernel [] true))
         (TxSuspension.loopback [] true))
    | actor_control_step

theorem fixture_packet_actor (family addr : Nat) (payload : List UInt8) (mtu tos : Nat) :
    Preserves (At (Covered locals crypt) crypt active) (Env.xmitPacket family addr payload mtu tos) := by
  unfold Env.xmitPacket
  repeat' actor_control_step

theorem fixture_packets_actor (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Preserves (At (Covered locals crypt) crypt active) (Env.xmitPackets family addr payload opts) := by
  unfold Env.xmitPackets
  repeat' first
    | (rx_retention_head Env.xmitPacket; exact fixture_packet_actor _ _ _ _ _)
    | actor_control_step

theorem inline_suspension : SameView TxSuspension.suspended Env.pollScheduledInline := by
  intro initial
  change Preserves (fun w=>TxSuspension.suspended w=initial) _
  unfold Env.pollScheduledInline
  simp (config:={zeta:=false}) only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (rx_retention_head rxPoll; exact TxSuspension.stack_poll _ _ initial)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w=>TxSuspension.suspended w=initial)
       intro pid state
       change Preserves (fun w=>TxSuspension.suspended w=initial) _)
    | (allocation_release_lift_from WG.M; exact TxSuspension.product TxSuspension.device initial)
    | (rx_retention_head unsupported; exact TxSuspension.product_unsupported _ initial)
    | routing_tx_step

theorem inline_poll_actor : Preserves (At (Covered locals crypt) crypt active) Env.pollScheduledInline :=
  At.product (fun _=>TxWorkNapi.inline locals) inline_suspension

open Lean Meta Elab Tactic in
elab "tx_actor_source " name:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Preserves do throwError "expected a preservation contract"
  let some raw := target.getAppArgs.back? | throwError "missing native action"
  let mut source := raw.consumeMData.headBeta
  let lifts := [``liftM, ``MonadLift.monadLift, ``MonadLiftT.monadLift,
    ``liftWG, ``liftRouting, ``liftAmbient]
  unless lifts.any source.isAppOf do throwError "expected a lifted native action"
  for _ in [:8] do
    if lifts.any source.isAppOf then
      let some inner := source.getAppArgs.back? | throwError "missing lifted source"
      source := inner.consumeMData.headBeta
  let expected ← realizeGlobalConstNoOverloadWithInfo name
  unless source.isAppOf expected do throwError "different native source"

macro "actor_traffic_step" : tactic => `(tactic| first
  | (rx_retention_head Env.fixtureSend; exact fixture_send_actor)
  | (rx_retention_head Env.senderSource; exact sender_source_actor _ _ _ _)
  | (rx_retention_head Env.xmitPackets; exact fixture_packets_actor _ _ _ _)
  | (rx_retention_head Env.xmitMulticastLoop; exact multicast_actor _ _)
  | (rx_retention_head Env.pollScheduledInline; exact inline_poll_actor)
  | (rx_retention_head Env.runWorker; apply run_worker_actor)
  | (tx_actor_source requireNotPending; exact pending_guard_actor _ _)
  | (tx_actor_source wgReceive; exact ingress_actor _ _)
  | (tx_actor_source wgXmit; exact transmit_actor _ _ _ _)
  | (tx_actor_source getDev; exact at_world TxActorFrames.device)
  | (tx_actor_source getPeer; exact at_world (TxActorFrames.peer _))
  | (allocation_release_lift_from Net.M
     apply actor_routing
     first
     | env_operation_fact TxSuspension.route
     | env_operation_fact TxSuspension.route_output
     | env_operation_fact TxSuspension.neighbour
     | (apply TxSuspension.socket_namespace
        first
        | env_operation_fact TxSuspension.route_output
        | env_operation_fact TxSuspension.neighbour))
  | actor_deferred_step
  | actor_control_step)

end Leanux.Proofs.WG.RetirementSecurity.TxWork
