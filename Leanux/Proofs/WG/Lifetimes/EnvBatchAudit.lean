import Leanux.Proofs.WG.Lifetimes.EnvTrafficAudit
import Leanux.Proofs.WG.Environment.BatchSource

/-! Original batch submission and its deferred continuation. Per-item CQEs,
captured device scalars, inline polling and scheduler probes retain their source
order. No successful draining or valid-input premise is used. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing

def batchItemAudit (d : Device) (cqes : List Int) (item : BatchItem) : AuditM (ForInStep (List Int)) := do
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
      auditFocus (liftWGObserver (wgReceivePrefix msg src))
      pollScheduledInlineAudit
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
        xmitMulticastLoopAudit family addr
        if family == 4 then liftPrefix (Net.neighbourClassify WG0_IFINDEX)
        let ret ← auditFocus (liftWGObserver (wgXmitPrefix family addr pkts mtu))
        cqes := cqes ++ [if ret == 0 then (payload.length : Int) else ret]
  return .yield cqes

def batchAudit (items : List BatchItem) : AuditM Int := do
  let some d := (← liftPrefix getWG).dev | liftPrefix (unsupported "a batch without wg0")
  if !d.running then liftPrefix (unsupported "a batch with wg0 down")
  for pid in d.peerList do liftPrefix (liftWG (requireNotPending pid "a batch while a handshake is queued"))
  let cqes ← forIn items ([] : List Int) (fun item cqes => batchItemAudit d cqes item)
  liftPrefix (modifyAmbient fun w => {w with extraOut := [("cqes", Lean.toJson cqes)]})
  afterBatchAudit
  return items.length


macro "env_batch_erasure" : tactic => `(tactic|
  first
    | (traffic_head afterBatchAudit; exact afterBatchAudit_erases)
    | (traffic_head pollScheduledInlineAudit; exact pollScheduledInlineAudit_erases)
    | (traffic_head xmitMulticastLoopAudit; exact xmitMulticastLoopAudit_erases _ _)
    | (traffic_head wgXmitPrefix; exact auditFocus_erases (liftWGObserver_erases (wgXmitPrefix_erases _ _ _ _)))
    | env_traffic_erasure
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq,
        Prod.mk.injEq, BatchItem.inject.injEq, BatchItem.xmit.injEq,
        Except.ok.injEq, Except.error.injEq, reduceCtorEq]; all_goals try subst_vars))

macro "env_batch_preservation" : tactic => `(tactic|
  first
    | (traffic_head afterBatchAudit; exact afterBatchAudit_preserves)
    | (traffic_head pollScheduledInlineAudit; exact pollScheduledInlineAudit_preserves)
    | (traffic_head xmitMulticastLoopAudit; exact xmitMulticastLoopAudit_preserves _ _)
    | (traffic_head wgXmitPrefix; exact auditFocus_preserves
        (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _).liftWGObserver)
    | (traffic_head routeLookup; exact auditLift_store _ (by
        intro initial
        exact productRouting_spec _ (fun store => store.2.2.2 = initial)))
    | (traffic_head xmitPackets; exact auditLift_store _
        ((xmitPackets_sameKernel _ _ _ _).of_factor (fun s : ProductStore43 => s.2.2.2)
          (fun w => wgStoreView w.wg) (fun _ => rfl)))
    | (traffic_head modifyAmbient; exact auditLift_store _ (by
        intro initial
        exact productAmbient_spec _ _ (fun _ _ hi => hi)))
    | env_traffic_preservation)

theorem batchItemAudit_erases (d : Device) (cqes : List Int) (item : BatchItem) :
    ErasesPrefix (batchItemAudit d cqes item) (Environment.batchItemSource d cqes item) := by
  unfold batchItemAudit Environment.batchItemSource
  repeat' env_batch_erasure

theorem batchItemAudit_preserves (d : Device) (cqes : List Int) (item : BatchItem) :
    PrefixPreserves AuditInv AuditSafe (batchItemAudit d cqes item) := by
  apply PrefixEnsures.preserves
  unfold batchItemAudit
  repeat' env_batch_preservation

theorem batchAudit_erases (items : List BatchItem) : ErasesPrefix (batchAudit items) (Env.batch items) := by
  rw [← Environment.batchSource_eq]
  unfold batchAudit Environment.batchSource
  repeat' first
    | (traffic_head batchItemAudit; exact batchItemAudit_erases _ _ _)
    | env_batch_erasure

theorem batchAudit_preserves (items : List BatchItem) : PrefixPreserves AuditInv AuditSafe (batchAudit items) := by
  apply PrefixEnsures.preserves
  unfold batchAudit
  repeat' first
    | (traffic_head batchItemAudit; exact batchItemAudit_preserves _ _ _)
    | env_batch_preservation

end Leanux.Proofs.WG.Lifetimes
