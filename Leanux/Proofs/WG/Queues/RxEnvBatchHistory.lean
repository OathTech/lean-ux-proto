import Leanux.Proofs.WG.Queues.RxEnvTrafficHistory
import Leanux.Proofs.WG.Lifetimes.EnvBatchAudit

/-! Original batch items and deferred processing retain actual poll placement.
Ingress and its inline poll share one NET_RX section; CQEs and captured device
scalars follow the original source on every normal or failed prefix. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def batchItem (d : Device) (cqes : List Int) (item : BatchItem) : Obs (ForInStep (List Int)) := do
  let mut cqes := cqes
  match item with
  | .inject family port msg =>
    if port != d.incomingPort then liftPrefix (unsupported "a batch datagram to a port other than wg0's")
    liftPrefix fixtureSend
    let src ← liftPrefix (senderSource family 0)
    if family == 4 then
      match ← liftPrefix (Net.routeOutput4 0 src.daddr) with
      | .error _ => liftPrefix (invariant "wg_batch: the datagram to wg0's port has no route")
      | .ok r =>
        if r.dev != LO_IFINDEX || r.src != src.saddr then
          liftPrefix (invariant "wg_batch: the route disagrees with the sender source")
        liftPrefix (Net.neighbourClassify LO_IFINDEX)
    runWorkerPrefix .netRx do
      mixed (liftWGObserver (wgReceivePrefix msg src))
      pollScheduledInline
    cqes := cqes ++ [(msg.length : Int)]
  | .xmit family addr payload opts =>
    match ← liftPrefix (Net.routeLookup family 0 addr) with
    | .error err => cqes := cqes ++ [err]
    | .ok r =>
      if r.dev != WG0_IFINDEX then liftPrefix (unsupported "a batch transmit to a local address (not into wg0)")
      if (family == 4 && !d.inet4Dev) || (family == 6 && !d.inet6Dev) then
        liftPrefix (unsupported "a transmit after an MTU change took the family's routes into wg0 down")
      liftPrefix fixtureSend
      let opts := { opts with routeMtu := opts.routeMtu <|> (if r.mtu != 0 then some r.mtu else none) }
      match ← liftPrefix (xmitPackets family addr payload opts) with
      | .error e => cqes := cqes ++ [e]
      | .ok (pkts, mtu) =>
        audit (xmitMulticastLoopAudit family addr)
        if family == 4 then liftPrefix (Net.neighbourClassify WG0_IFINDEX)
        let ret ← mixed (liftWGObserver (wgXmitPrefix family addr pkts mtu))
        cqes := cqes ++ [if ret == 0 then (payload.length : Int) else ret]
  return .yield cqes

def batch (items : List BatchItem) : Obs Int := do
  let some d := (← liftPrefix getWG).dev | liftPrefix (unsupported "a batch without wg0")
  if !d.running then liftPrefix (unsupported "a batch with wg0 down")
  for pid in d.peerList do liftPrefix (liftWG (requireNotPending pid "a batch while a handshake is queued"))
  let cqes ← forIn items ([] : List Int) (fun item cqes => batchItem d cqes item)
  liftPrefix (modifyAmbient fun w => {w with extraOut := [("cqes", Lean.toJson cqes)]})
  afterBatch
  return items.length

macro "rx_env_batch_erasure" : tactic => `(tactic|
  first
    | (rx_env_traffic_head afterBatch; exact afterBatch_erases)
    | (rx_env_traffic_head xmitMulticastLoopAudit; exact audit_erases (xmitMulticastLoopAudit_erases _ _))
    | (rx_env_traffic_head wgXmitPrefix; exact mixed_erases (liftWGObserver_erases (wgXmitPrefix_erases _ _ _ _)))
    | rx_env_traffic_erasure)

macro "rx_env_batch_preservation" : tactic => `(tactic|
  first
    | (rx_env_traffic_head afterBatch; exact afterBatch_preserves)
    | (rx_env_traffic_head xmitMulticastLoopAudit; exact audit_preserves _ (xmitMulticastLoopAudit_preserves _ _))
    | (rx_env_traffic_head wgXmitPrefix; exact mixed_preserves
        (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _).liftWGObserver)
    | (rx_env_traffic_head routeLookup; exact boundaryLift_kernel _
        (by intro initial; exact productRouting_spec _ (fun store => store = initial)))
    | (rx_env_traffic_head xmitPackets; exact boundaryLift_kernel _ (xmitPackets_sameKernel _ _ _ _))
    | (rx_env_traffic_head modifyAmbient; exact boundaryLift_kernel _
        (by intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi)))
    | rx_env_traffic_preservation)

macro "rx_env_batch_projection" : tactic => `(tactic|
  first
    | (audit_contract ProjectsUnder; first
        | (rx_env_traffic_head afterBatch; exact afterBatch_projects)
        | (rx_env_traffic_head xmitMulticastLoopAudit; exact audit_projects (xmitMulticastLoopAudit_preserves _ _))
        | (rx_env_traffic_head wgXmitPrefix; exact mixed_projects
            (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _).liftWGObserver))
    | (audit_contract PrefixPreserves; env_batch_preservation)
    | (audit_contract PrefixEnsures; env_batch_preservation)
    | rx_env_traffic_projection)

theorem batchItem_erases (d : Device) (cqes : List Int) (item : BatchItem) : ErasesPrefix (batchItem d cqes item) (Environment.batchItemSource d cqes item) := by
  cases item
  all_goals
    unfold batchItem Environment.batchItemSource
    repeat' rx_env_batch_erasure
  all_goals contradiction

theorem batchItem_preserves (d : Device) (cqes : List Int) (item : BatchItem) : PrefixPreserves BoundaryInv BoundarySafe (batchItem d cqes item) := by
  cases item
  all_goals
    unfold batchItem
    repeat' rx_env_batch_preservation

theorem batchItem_projects (d : Device) (cqes : List Int) (item : BatchItem) : ProjectsUnder AuditInv auditEvent (batchItem d cqes item) (batchItemAudit d cqes item) := by
  cases item
  all_goals
    unfold batchItem batchItemAudit
    repeat' rx_env_batch_projection

theorem batch_erases (items : List BatchItem) : ErasesPrefix (batch items) (Env.batch items) := by
  rw [← Environment.batchSource_eq]
  unfold batch Environment.batchSource
  repeat' first
    | (rx_env_traffic_head batchItem; exact batchItem_erases _ _ _)
    | rx_env_batch_erasure

theorem batch_preserves (items : List BatchItem) : PrefixPreserves BoundaryInv BoundarySafe (batch items) := by
  unfold batch
  repeat' first
    | (rx_env_traffic_head batchItem; exact batchItem_preserves _ _ _)
    | rx_env_batch_preservation

theorem batch_projects (items : List BatchItem) : ProjectsUnder AuditInv auditEvent (batch items) (batchAudit items) := by
  unfold batch batchAudit
  repeat' first
    | (audit_contract ProjectsUnder; rx_env_traffic_head batchItem; exact batchItem_projects _ _ _)
    | (audit_contract PrefixPreserves; rx_env_traffic_head batchItemAudit; exact batchItemAudit_preserves _ _ _)
    | (audit_contract PrefixEnsures; rx_env_traffic_head batchItemAudit; exact batchItemAudit_preserves _ _ _)
    | rx_env_batch_projection

end Leanux.Proofs.WG.Queues.RxHistory
