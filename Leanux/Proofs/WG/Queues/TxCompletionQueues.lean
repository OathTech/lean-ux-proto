import Leanux.Proofs.WG.Queues.TxCompletionReservation
import Leanux.Proofs.WG.Queues.HolderWorkFrames

/-! Logical TX queue retention through the actual send/timer/freshness path.
The supplied durable handoff is accounted separately; this file does not infer
credit from queue membership or require final peer survival. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.TxReservation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

private def TxRetained (initial w : WGWorld) : Prop :=
  ∀ pid batches, handoffTxView w pid = some batches → handoffTxView initial pid = some batches

private theorem tx_frame {α : Type} (action : WG.M α)
    (frame : ∀ initial, Preserves (Frame initial) action) (initial) :
    Preserves (TxRetained initial) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  have step := (hoare_iff_run_ambient _ _ _).mp (frame w) w a result v b (Frame.refl w) hr
  exact fun pid xs found => hi pid xs (step.tx pid xs found)

private theorem tx_read_bind (initial : WGWorld) {α : Type} (pid : PeerId) (f : Peer → WG.M α)
    (hf : ∀ p, handoffTxView initial pid = some p.txQueue.all →
      Preserves (TxRetained initial) (f p)) :
    Preserves (TxRetained initial) (getPeer pid >>= f) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨p,read,mid,hread,hr⟩ := hr
  obtain ⟨readEq,midEq,d,hd,hp⟩ := getPeer_normal pid w read p a mid hread
  subst read
  subst mid
  exact (hoare_iff_run_ambient _ _ _).mp (hf p (hi pid p.txQueue.all
    (by simp [handoffTxView,hd,hp]))) w a result v b hi hr

private theorem tx_set_saved (initial : WGWorld) (pid : PeerId) (p : Peer)
    (saved : handoffTxView initial pid = some p.txQueue.all) :
    Preserves (TxRetained initial) (setPeer pid p) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  cases hr
  intro q batches found
  cases hd : w.dev with
  | none => simp [handoffTxView,hd] at found
  | some d =>
    simp only [handoffTxView,hd,Option.map_some,Option.bind_some,
      Std.TreeMap.getElem?_insert,Std.LawfulEqOrd.compare_eq_iff_eq] at found
    by_cases same : pid = q
    · subst q
      simp only [ite_true,Option.map_some,Option.some.injEq] at found
      exact found ▸ saved
    · apply hi q batches
      simpa only [handoffTxView,hd,Option.bind_some,ite_eq_right same] using found

macro "tx_retained_step " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (env_bind_head getPeer; apply tx_read_bind $initial; intro p saved)
  | (rx_retention_head setPeer; apply tx_set_saved $initial; assumption)
  | (rx_retention_head getPeer
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a p v b hi hr
     simpa only [(getPeer_normal _ w v p a b hr).1] using hi)
  | (rx_retention_head peerPut; exact tx_frame _ (HolderWorkFrames.peerPut_frame _) $initial)
  | (rx_retention_head modifyDev
     apply hoare_modify
     intro w hi q xs found
     apply hi q xs
     simpa only [handoffTxView,Option.bind_map,Function.comp_def] using found)
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (TxRetained $initial))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | rx_retention_step)

private theorem queued_tx (pid : PeerId) (retry : Bool) (initial) :
    Preserves (TxRetained initial) (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation peerGet refcountInc
  simp (config := {zeta := false}) only [requireNotPending,branch,branchCmp,
    unsupported,peekQueuedUnit,recordQueued]
  repeat' tx_retained_step initial

private theorem fresh_tx (pid : PeerId) (initial) :
    Preserves (TxRetained initial) (keepKeyFresh pid) :=
  keepKeyFresh_preserves _ pid (queued_tx pid false initial)

private theorem sendSkb_frame (pid : PeerId) (bytes : List UInt8) (ds : Nat) (initial) :
    Preserves (Frame initial) (sendSkbToPeer pid bytes ds) := by
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head send4
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.send4_frame) _ _ _ _ _ initial)
    | (rx_retention_head send6
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.send6_frame) _ _ _ _ _ initial)
    | holder_work_step initial

private theorem dataSent_frame (pid : PeerId) (initial) :
    Preserves (Frame initial) (timersDataSent pid) := by
  unfold timersDataSent modPeerTimerGuard WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (Frame initial))
    | (rx_retention_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (Frame initial))
    | (rx_retention_head armTimer
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.arm_preserves) _ _ _ _ initial)
    | holder_work_step initial

private theorem prefix_frame (pid : PeerId) (item : List SkbId) (initial) :
    Preserves (Frame initial) (completionPrefix pid item) := by
  unfold completionPrefix WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Frame initial)
       intro x b
       change Preserves (Frame initial) _)
    | (rx_retention_head timersTraversal
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.timersTraversal_frame) _ initial)
    | (rx_retention_head timersAnyAuthenticatedPacketSent
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.timersAnyAuthenticatedPacketSent_frame) _ initial)
    | (rx_retention_head getTxSkb
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a pkt v b hi hr
       simpa only [(Packets.getTxSkb_current _ w v pkt a b hr).1] using hi)
    | (rx_retention_head sendSkbToPeer; exact sendSkb_frame _ _ _ initial)
    | (rx_retention_head timersDataSent; exact dataSent_frame _ initial)
    | holder_work_step initial

private theorem completion_tx (pid : PeerId) (item : List SkbId) (initial) :
    Preserves (TxRetained initial) (createDataDone pid item) := by
  rw [completion_factor]
  exact preserves_bind (tx_frame _ (prefix_frame pid item) initial) (fun _ => fresh_tx pid initial)

private theorem tx_equal (retained : TxRetained w v) (base : baseView v = baseView w) :
    handoffTxView v = handoffTxView w := by
  funext q
  cases hv : handoffTxView v q with
  | some batches => exact (retained q batches hv).symm
  | none =>
    have cells := congrFun (congrArg Prod.snd base) q
    unfold baseView handoffTxView at *
    cases hw : w.dev.bind (fun d => d.peers[q]?) <;>
      cases hv' : v.dev.bind (fun d => d.peers[q]?) <;> simp_all

theorem keepKeyFresh_queues (pid : PeerId) : SameView handoffTxView (keepKeyFresh pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  cases result
  have retained := (hoare_iff_run_ambient _ _ _).mp (fresh_tx pid w)
    w a () v b (fun _ _ h => h) hr
  obtain ⟨delta,step⟩ := (Transfers.iff_run_ambient _).mp (keepKeyFresh_transfers pid)
    w a () v b hr
  exact tx_equal retained step.base

theorem createDataDone_queues (pid : PeerId) (item : List SkbId) :
    SameView handoffTxView (createDataDone pid item) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  cases result
  have retained := (hoare_iff_run_ambient _ _ _).mp (completion_tx pid item w)
    w a () v b (fun _ _ h => h) hr
  rw [completion_factor,MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,sent,mid,hprefix,hfresh⟩ := hr
  cases u
  have before := (ProjectedAction.iff_run_ambient _ _ _).mp
    (completionPrefix_base pid item) w a () sent mid hprefix
  obtain ⟨delta,step⟩ := (Transfers.iff_run_ambient _).mp (keepKeyFresh_transfers pid)
    sent mid () v b hfresh
  exact tx_equal retained (step.base.trans before)

/-- The entire concrete prefix has an empty handoff, including its actual
socket/cache/timer writes. This exposes the earlier input cut without changing
or replacing the original source. -/
theorem completionPrefix_protect (pid : PeerId) (item : List SkbId) :
    SameView protectView (completionPrefix pid item) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  have carrier := (ProjectedAction.iff_run_ambient _ _ _).mp
    (completionPrefix_carrier pid item) w a result v b hr
  have peers := congrArg Prod.fst carrier
  have rx := congrArg (fun x => x.2.1) carrier
  have sends := (ProjectedAction.iff_run_ambient _ _ _).mp
    (completionPrefix_send pid item) w a result v b hr
  have retained := (hoare_iff_run_ambient _ _ _).mp
    (tx_frame _ (prefix_frame pid item) w) w a result v b (fun _ _ h => h) hr
  have queues := tx_equal retained (base_of_peerView peers)
  exact Prod.ext peers (Prod.ext rx (Prod.ext queues sends))

/-- An unchanged actual TX queue cannot carry a newly charged batch. Funding
rules out owners whose absent peer would otherwise hide a fictitious append. -/
theorem handoff_tx_nil (step : Handoff w v [] [] delta)
    (queues : handoffTxView v = handoffTxView w)
    (funded : CarrierState cs (loans ++ delta.owners) v) : delta.tx = [] := by
  cases ht : delta.tx with
  | nil => rfl
  | cons t rest =>
    have positive : 0 < demand cs (loans ++ delta.owners) t.owner := by
      simp [demand,HandoffDelta.owners,ht,List.count_append]
      <;> omega
    obtain ⟨p,hp,_⟩ := protected_resident funded.funded positive
    obtain ⟨d,hd,_,stored,_⟩ := resident_fields hp
    have present : handoffTxView v t.owner.slot = some p.txQueue.all := by
      simp [handoffTxView,hd,stored]
    have old : handoffTxView w t.owner.slot = some p.txQueue.all := queues ▸ present
    have append := step.tx t.owner.slot
    rw [present,old] at append
    have eq : p.txQueue.all = p.txQueue.all ++ delta.items t.owner.slot := Option.some.inj append
    have len := congrArg List.length eq
    have empty : delta.items t.owner.slot = [] := by
      cases he : delta.items t.owner.slot with
      | nil => rfl
      | cons x xs =>
        simp only [he,List.length_append,List.length_cons] at len
        omega
    have member : t.item ∈ delta.items t.owner.slot := by
      simp [HandoffDelta.items,ht]
    rw [empty] at member
    cases member

/-- Funded completion can be anchored at its actual original input, before
socket and timer effects, with precisely the same freshness delta. -/
theorem createDataDone_handoff (pid : PeerId) (item : List SkbId)
    (hi : ClearWork.Inv cs loans w) (a b : Ambient)
    (hr : ((createDataDone pid item).run w).run a = .ok (((),v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧ delta.tx = [] ∧
      ClearWork.Inv cs (loans ++ delta.owners) v := by
  obtain ⟨sent,middle,delta,hprefix,hfresh,step,_,funded⟩ :=
    createDataDone_funded pid item hi a b hr
  have prefixView := (ProjectedAction.iff_run_ambient _ _ _).mp
    (completionPrefix_protect pid item) w a () sent middle hprefix
  have whole : Handoff w v [] [] delta := by
    simpa only [HandoffDelta.append,List.nil_append] using
      (handoff_of_view prefixView).trans step
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp
    (createDataDone_queues pid item) w a () v b hr
  exact ⟨delta,whole,handoff_tx_nil whole queues funded.1,funded⟩

theorem fresh_funded_send_only (pid : PeerId) (hi : ClearWork.Inv cs loans w)
    (a b : Ambient) (hr : ((keepKeyFresh pid).run w).run a = .ok (((),v),b)) :
    ∃ delta, Handoff w v [] [] delta ∧ delta.tx = [] ∧ ClearWork.Inv cs (loans ++ delta.owners) v := by
  obtain ⟨delta,step,funded,stable⟩ := keepKeyFresh_funded pid hi.1 hi.2 a b hr
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp (keepKeyFresh_queues pid) w a () v b hr
  exact ⟨delta,step,handoff_tx_nil step queues funded,funded,stable⟩

/-- The chosen freshness witness has only send reservations, and the actual
batch payment leaves those reservations charged. -/
theorem completion_dispose_send_only (o : Owner) (item : List SkbId) (key : KeypairId)
    (hi : ClearWork.Inv cs (o :: loans) w) (a b : Ambient)
    (hr : (((do createDataDone o.slot item
                TxDisposition.disposeSource o.slot item key) : WG.M Bool).run w).run a =
      .ok ((result,v),b)) :
    result = true ∧ ∃ delta : HandoffDelta,
      delta.tx = [] ∧ ClearWork.Inv cs (loans ++ delta.owners) v ∧
      sendView v = (sendView w).map (· ++ delta.send.map Owner.slot) := by
  rw [MaterialOrigin.bind_ok_ambient] at hr
  obtain ⟨u,completed,middle,hcomplete,hdispose⟩ := hr
  cases u
  obtain ⟨sent,freshAt,delta,_,hfresh,step,sends,funded⟩ :=
    createDataDone_funded o.slot item hi a middle hcomplete
  have txFrame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (keepKeyFresh_queues o.slot) sent freshAt () completed middle hfresh
  have noTx := handoff_tx_nil step txFrame funded.1
  have paid := dispose_normal o item key (loans := loans ++ delta.owners)
    (by simpa only [List.cons_append] using funded) middle b hdispose
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp
    (dispose_workQueues o.slot item key) completed middle result v b hdispose
  have sendFrame : sendView v = sendView completed := by
    simpa only [sendView,WorkQueueFrames.view,Option.map_map,Function.comp_def] using
      congrArg (Option.map fun q => q.2.1) queues
  exact ⟨paid.1,delta,noTx,paid.2,sendFrame.trans sends⟩

end Leanux.Proofs.WG.Queues.RxCredits.TxReservation
