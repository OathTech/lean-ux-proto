import Leanux.Proofs.WG.Queues.TxFreshReservation
import Leanux.Proofs.WG.Queues.SendWork
import Leanux.Proofs.WG.Queues.TxQueueDebit

/-! The encrypted batch's actual send prefix precedes its conditional fresh-key
handoff. Socket errors remain normal no-send outcomes; all recorded guards and
clock/timer failures remain the original partial executions. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.TxReservation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private abbrev completionView :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.view)

/-- Literal send/timer prefix before the final freshness call. -/
def completionPrefix (pid : PeerId) (item : List SkbId) : WG.M Unit := do
  timersTraversal pid
  timersAnyAuthenticatedPacketSent pid
  let mut dataSent := false
  for id in item do
    let skb ← getTxSkb id
    _ ← branch .doneSkbIterate true
    let isKeepalive := skb.bytes.length == MESSAGE_DATA_LEN_0
    let sent ← sendSkbToPeer pid skb.bytes skb.ds
    if ← WG.andM (branch .doneSendOk sent) (branch .doneNotKeepalive !isKeepalive) then dataSent := true
  _ ← branch .doneSkbIterate false
  if ← branch .doneDataSent dataSent then timersDataSent pid

theorem completion_factor (pid : PeerId) (item : List SkbId) :
    createDataDone pid item = (do completionPrefix pid item; keepKeyFresh pid) := by
  simp only [createDataDone,completionPrefix,bind_assoc,bind_if_source,pure_bind]

private theorem sendSkb_view (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    SameView completionView (sendSkbToPeer pid bytes ds) := by
  intro initial
  change Preserves (fun w => completionView w = initial) _
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4
       exact ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.send4_view) _ _ _ _ _).wp (fun s => s = initial))
    | (rx_retention_head send6
       exact ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.send6_view) _ _ _ _ _).wp (fun s => s = initial))
    | send_work_step initial

private theorem dataSent_view (pid : PeerId) : SameView completionView (timersDataSent pid) := by
  have arm : ∀ (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64),
      SameView completionView (armTimer pid timer delay jc) := by
    run_tac do
      let n := Lean.mkCIdent (normalizePinnedName
        `_private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.armTimer_view)
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact @$n))
  intro initial
  change Preserves (fun w => completionView w = initial) _
  unfold timersDataSent
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head callerJiffies
       exact (callerJiffies_sameWGWorld _).wp (fun w => completionView w = initial))
    | (rx_retention_head jitterBelowRekeyTimeout
       exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (fun w => completionView w = initial))
    | (rx_retention_head modPeerTimerGuard
       exact ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.modPeerTimerGuard_view) _).wp (fun s => s = initial))
    | send_work_step initial
  all_goals
    rename_i jc jitter ready hready
    exact (arm pid .newHandshake _ jc).wp (fun s => s = initial)

private theorem prefix_view (pid : PeerId) (item : List SkbId) :
    SameView completionView (completionPrefix pid item) := by
  have getter (id : SkbId) : SameView completionView (getTxSkb id) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a pkt v b hr
    exact congrArg completionView (Packets.getTxSkb_current id w v pkt a b hr).1
  intro initial
  change Preserves (fun w => completionView w = initial) _
  unfold completionPrefix WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => completionView w = initial)
       intro x b
       change Preserves (fun w => completionView w = initial) _)
    | (rx_retention_head timersTraversal
       exact ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.timersTraversal_view) _).wp (fun s => s = initial))
    | (rx_retention_head timersAnyAuthenticatedPacketSent
       exact ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.timersAnyAuthenticatedPacketSent_view) _).wp (fun s => s = initial))
    | (rx_retention_head getTxSkb; exact (getter _).wp (fun s => s = initial))
    | (rx_retention_head sendSkbToPeer; exact (sendSkb_view _ _ _).wp (fun s => s = initial))
    | (rx_retention_head timersDataSent; exact (dataSent_view _).wp (fun s => s = initial))
    | send_work_step initial

theorem completionPrefix_preserves (pid : PeerId) (item : List SkbId) :
    Preserves (ClearWork.Inv cs loans) (completionPrefix pid item) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp (prefix_view pid item) w a result v b hr
  have carrier := (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrier_factor)
  have stable := (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.stable_factor)
  exact ⟨hi.1.view ((carrier v).trans ((congrArg
    (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrierOf)
    frame).trans (carrier w).symm)),
    hi.2.view ((stable v).trans ((congrArg
    (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.stableOf)
    frame).trans (stable w).symm))⟩

/-- The send prefix retains every peer's identity and RX queue, including
presence. This is separate from the subsequent freshness handoff. -/
theorem completionPrefix_carrier (pid : PeerId) (item : List SkbId) :
    SameView carrierView (completionPrefix pid item) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp (prefix_view pid item) w a result v b hr
  have factor := (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrier_factor)
  have eq := (factor v).trans ((congrArg
    (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.carrierOf)
    frame).trans (factor w).symm)
  exact eq

theorem completionPrefix_base (pid : PeerId) (item : List SkbId) :
    SameView baseView (completionPrefix pid item) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (completionPrefix_carrier pid item) w a result v b hr
  exact base_of_peerView (congrArg Prod.fst frame)

theorem completionPrefix_send (pid : PeerId) (item : List SkbId) :
    SameView sendView (completionPrefix pid item) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  have frame := (ProjectedAction.iff_run_ambient _ _ _).mp (prefix_view pid item) w a result v b hr
  have projected := congrArg (Option.map
    (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.State.sendQueue)) frame
  have factor (x : WGWorld) : sendView x =
      Option.map (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.State.sendQueue) (completionView x) := by
    cases x with
    | mk => simp only [sendView,completionView]; cases ‹Option Device› <;> rfl
  exact (factor v).trans (projected.trans (factor w).symm)

/-- The actual completed prefix supplies the exact input to freshness. Its
new durable delta remains charged, even when socket sends returned errors. -/
theorem createDataDone_funded (pid : PeerId) (item : List SkbId)
    (hi : ClearWork.Inv cs loans w) (a b : Ambient)
    (hr : ((createDataDone pid item).run w).run a = .ok (((),v),b)) :
    ∃ sent middle delta,
      ((completionPrefix pid item).run w).run a = .ok (((),sent),middle) ∧
      ((keepKeyFresh pid).run sent).run middle = .ok (((),v),b) ∧
      Handoff sent v [] [] delta ∧
      sendView v = (sendView w).map (· ++ delta.send.map Owner.slot) ∧
      ClearWork.Inv cs (loans ++ delta.owners) v := by
  rw [completion_factor,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,sent,middle,hprefix,hfresh⟩ := hr
  cases u
  have preserved := (hoare_iff_run_ambient _ _ _).mp (completionPrefix_preserves pid item)
    w a () sent middle hi hprefix
  obtain ⟨delta,step,funded,stable⟩ := keepKeyFresh_funded pid preserved.1 preserved.2 middle b hfresh
  have sends := (ProjectedAction.iff_run_ambient _ _ _).mp
    (completionPrefix_send pid item) w a () sent middle hprefix
  exact ⟨sent,middle,delta,hprefix,hfresh,step,by rw [step.send,sends],funded,stable⟩

/-- Payment and packet disposal do not remove durable work occurrences. -/
theorem dispose_workQueues (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    SameView WorkQueueFrames.view (TxDisposition.disposeSource pid item key) := by
  have frees : SameView WorkQueueFrames.view (TxDisposition.freeList item) := by
    have leaf (id : SkbId) : SameView WorkQueueFrames.view (freeTxSkb id) := by
      intro initial
      unfold freeTxSkb
      apply hoare_liftSkb
      intro w d store hi hd
      simpa only [WorkQueueFrames.view,hd,Option.map_some] using hi
    induction item with
    | nil => simpa only [TxDisposition.freeList_nil] using SameView.pure WorkQueueFrames.view ()
    | cons id rest ih =>
      rw [TxDisposition.freeList_cons]
      exact (leaf id).bind fun _ => ih
  have factor : TxDisposition.disposeSource pid item key = (do
    TxDisposition.freeList item
    keypairPut (some key) false
    peerPut (some pid)
    pure true : WG.M Bool) := by
    simp only [TxDisposition.disposeSource,TxDisposition.freeList,bind_assoc,pure_bind]
  rw [factor]
  exact frees.bind fun _ => (WorkQueueFrames.keypairPut_frame (some key) false).bind fun _ =>
    (WorkQueueFrames.peerPut_frame (some pid)).bind fun _ => SameView.pure _ true

/-- Completed encrypted data is disposed and pays exactly its supplied batch
reservation. The freshness delta remains charged after that payment. -/
theorem completion_dispose_normal (o : Owner) (item : List SkbId) (key : KeypairId)
    (hi : ClearWork.Inv cs (o :: loans) w) (a b : Ambient)
    (hr : (((do createDataDone o.slot item
                TxDisposition.disposeSource o.slot item key) : WG.M Bool).run w).run a =
      .ok ((result,v),b)) :
    result = true ∧ ∃ delta : HandoffDelta,
      ClearWork.Inv cs (loans ++ delta.owners) v ∧
      sendView v = (sendView w).map (· ++ delta.send.map Owner.slot) := by
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,completed,middle,hcomplete,hdispose⟩ := hr
  cases u
  obtain ⟨sent,freshAt,delta,_,_,_,sends,funded⟩ :=
    createDataDone_funded o.slot item hi a middle hcomplete
  have paid := dispose_normal o item key (loans := loans ++ delta.owners)
    (by simpa only [List.cons_append] using funded) middle b hdispose
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp
    (dispose_workQueues o.slot item key) completed middle result v b hdispose
  have sendFrame : sendView v = sendView completed := by
    simpa only [sendView,WorkQueueFrames.view,Option.map_map,Function.comp_def] using
      congrArg (Option.map fun q => q.2.1) queues
  exact ⟨paid.1,delta,paid.2,sendFrame.trans sends⟩

end Leanux.Proofs.WG.Queues.RxCredits.TxReservation
