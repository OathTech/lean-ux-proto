import Leanux.Proofs.WG.RetirementSecurity.TxWorkDecrypt

/-! The native decrypt worker preserves active/suspended TX obligations at
both NAPI placements and the scheduler checkpoint. Native RX publication
changes receive work only; no worker callback premise remains. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

namespace TxSuspension
theorem set_rx_packet (skb : SkbId) (f : RxPacket→RxPacket) : Keeps (setRxSkb skb f) := by
  apply skb_lift
  suspension_source [SkbStore.setRx,SkbStore.getRx] using [invariant]

theorem decrypt_packet (pkt : RxPacket) : Keeps (decryptPacket pkt) := by
  suspension_source [decryptPacket,WG.orM] using [branch,key,expired,compare,set_key,allocation,invariant]

theorem rx_publish (skb : SkbId) (state : PacketState) : Keeps (RxWorkers.publishSource skb state) := by
  suspension_source [RxWorkers.publishSource] using [rx_packet,owner_deref,peer_get,peer,invariant,set_rx_packet,set_peer]

theorem decrypt_prepare : Keeps RxWorkers.prepareSource := by
  suspension_source [RxWorkers.prepareSource] using [device,branch,modify_device,rx_packet,decrypt_packet,
    set_rx_packet,rx_publish,invariant]
end TxSuspension

namespace TxWork
theorem decrypt_prepare_actor : Preserves (At (Covered locals crypt) crypt active) (liftWG RxWorkers.prepareSource) :=
  At.native (fun _=>serving_decrypt_prepare) TxSuspension.decrypt_prepare

theorem peer_put_actor (pid : Option PeerId) : Preserves (At (Covered locals crypt) crypt active) (liftWG (peerPut pid)) :=
  At.native (fun _=>serving_peer_put pid) (TxSuspension.peer_put pid)

theorem decrypt_step : Preserves (At (Covered locals crypt) crypt active)
    (decryptStep Env.napiSoftirq Env.napiIrqExit) := by
  rw [←RxWorkers.decrypt_source]
  unfold RxWorkers.decryptSource
  apply preserves_bind napi_actor
  intro _
  apply preserves_bind decrypt_prepare_actor
  intro result
  cases result with
  | none=>exact preserves_pure false
  | some pid=>
    exact preserves_bind irq_exit_actor fun _=>preserves_bind (peer_put_actor (some pid)) fun _=>
      preserves_bind napi_actor (fun _=>preserves_pure true)

theorem actor_reschedule (worker : Worker) : Preserves (At P crypt active) (Env.condResched worker) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  exact before.frame ((ProjectedAction.iff_run _ _ _).mp (reschedule worker) w result v run)

theorem actor_branch (decision : Decision) (value : Bool) :
    Preserves (At P crypt active) (Leanux.branch decision value : Leanux.M Bool) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  cases run
  exact before

theorem decrypt_iteration : Preserves (At (Covered locals crypt) crypt active)
    (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) := by
  let P:=At (Covered locals crypt) crypt active
  have next:Preserves P (decryptStep Env.napiSoftirq Env.napiIrqExit) := decrypt_step
  have need:Preserves P (Env.condResched .decryptWorker) := actor_reschedule .decryptWorker
  have decision (d : Decision) (value : Bool) : Preserves P (Leanux.branch d value : Leanux.M Bool) := actor_branch d value
  change Preserves P _
  routing_tx_source [decryptIter,workerIter] using [next,need,decision]
end TxWork

end Leanux.Proofs.WG.RetirementSecurity
