import Leanux.Proofs.WG.Queues.BaseCoherenceCompletion
import Leanux.Proofs.WG.Queues.CurrentSlotStack

/-! The actual Stack transmit path and arbitrary-product poll callbacks retain
only the native base list and public-key rows. Resident peer deletion is allowed;
all source guards, recorded failures and negative status returns remain. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem lookupDst_structure (family addr : Nat) : SameView view (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  exact (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherence.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.borrow_view)
    ((hoare_iff_run_ambient _ _ _).mp (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run)

private theorem trim_structure (pid : PeerId) : SameView view (xmitTrim pid) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold xmitTrim
  simp (config := {zeta := false}) only [branch,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' base_rx_step initial

private theorem splice_structure (pid : PeerId) (packets : List WG.Packet) :
    SameView view (xmitSplice pid packets) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold xmitSplice
  repeat' base_rx_step initial

theorem wgXmit_view (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    SameView view (wgXmit family addr packets mtu) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  rw [wgXmitSource_eq]
  unfold wgXmitSource WG.andM
  simp (config := {zeta := false}) only [branch,invariant,skipCutSites,envOk]
  repeat' first
    | (rx_retention_head lookupDst; exact (lookupDst_structure _ _).wp (fun s => s=initial))
    | (rx_retention_head xmitTrim; exact (trim_structure _).wp (fun s => s=initial))
    | (rx_retention_head xmitSplice; exact (splice_structure _ _).wp (fun s => s=initial))
    | (rx_retention_head sendStagedPackets; exact (staged_view _).wp (fun s => s=initial))
    | (rx_retention_head loopbackSend; exact (store_view (loopbackSend_kernel _ _)).wp (fun s => s=initial))
    | (allocation_release_lift_from Net.M; exact hoare_liftRouting _ _ (fun _ _ hi => hi))
    | base_rx_step initial

theorem product_store_view {α : Type} {a : Leanux.M α} (same : SameProductStore a) :
    SameView (fun w : World => view w.wg) a :=
  same.of_factor (fun s : ProductStore43 => view {dev:=s.2.2.2.dev}) _ (fun _ => rfl)

theorem reply4_view (dst : Nat) (bytes : List UInt8) :
    SameView (fun w : World => view w.wg) (Leanux.Env.Stack.reply4 dst bytes) := by
  intro initial
  change Preserves (fun w : World => view w.wg=initial) _
  let P := fun w : World => view w.wg=initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : Leanux.M α) :=
    PublicationPoll.native_product _ _ ((store_view (liftRouting_sameWGStore a)).wp (fun s => s=initial))
  have dev : Preserves P (monadLift getDev : Leanux.M Device) :=
    PublicationPoll.native_product _ _ ((store_view getDev_sameWGStore).wp (fun s => s=initial))
  have send (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
      Preserves P (monadLift (wgXmit family addr packets mtu) : Leanux.M Int) :=
    PublicationPoll.native_product _ _ ((wgXmit_view family addr packets mtu).wp (fun s => s=initial))
  have discarded {α : Type} (a : Leanux.M α) (ha : Preserves P a) : Preserves P (Functor.discard a) :=
    discard_view_spec id P a ha
  rxstack_preserves_source [Leanux.Env.Stack.reply4,skipCut,unsupported]
    using [dev,send,ambient,routing,discarded]

theorem receive4_view (bytes : List UInt8) :
    SameView (fun w : World => view w.wg) (Leanux.Env.Stack.receive4 bytes) := by
  intro initial
  change Preserves (fun w : World => view w.wg=initial) _
  let P := fun w : World => view w.wg=initial
  have stopped (a : Leanux.M Unit) (hs : ∀ w, ∃ e, a.run w = .error e)
      (next : Unit → Leanux.M Unit) : Preserves P (a >>= next) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentStack.«0».Leanux.Proofs.WG.CurrentStack.stopped_bind) a hs next P
  have excluded := fun row tail => stopped (Leanux.Env.Stack.excluded row)
    (stackExcluded_failure row) tail
  have invalid := fun why tail => stopped (Leanux.invariant why) (fun _ => ⟨_,rfl⟩) tail
  have unsupported := fun why tail => stopped (Leanux.unsupported why) (fun _ => ⟨_,rfl⟩) tail
  have excludedAlone (row : String) : Preserves P (Leanux.Env.Stack.excluded row) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    obtain ⟨e,he⟩ := stackExcluded_failure row w
    rw [he] at hr
    contradiction
  have route (src dst : Nat) : Preserves P
      (monadLift (monadLift (Net.routeInput4 src dst) : WG.M _) : Leanux.M _) :=
    PublicationPoll.native_product _ _ ((store_view (liftRouting_sameWGStore _)).wp (fun s => s=initial))
  have read : Preserves P (getWG : Leanux.M WGWorld) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    cases hr
    exact hi
  have write (f : EnvWorld → EnvWorld) : Preserves P (modifyEnv f) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    cases hr
    exact hi
  unfold Leanux.Env.Stack.receive4
  repeat' first
    | (env_bind_head Leanux.Env.Stack.excluded; exact excluded _ _)
    | (env_bind_head Leanux.invariant; exact invalid _ _)
    | (env_bind_head Leanux.unsupported; exact unsupported _ _)
    | (allocation_release_head Leanux.Env.Stack.excluded; exact excludedAlone _)
    | (allocation_release_head Leanux.Env.Stack.reply4; exact (reply4_view _ _).wp (fun s => s=initial))
    | (allocation_release_head MonadLift.monadLift; exact route _ _)
    | (allocation_release_head liftM; exact route _ _)
    | (allocation_release_head getWG; exact read)
    | (allocation_release_head modifyEnv; exact write _)
    | rx_retention_step
    | env_ordinary_head_reduce
    | env_ordinary_head_match

theorem deliverInner_view (bytes : List UInt8) :
    SameView (fun w : World => view w.wg) (Leanux.Env.deliverInner bytes) := by
  intro initial
  change Preserves (fun w : World => view w.wg=initial) _
  have h4 : Preserves (fun w : World => view w.wg=initial) (Leanux.Env.Stack.receive4 bytes) := (receive4_view bytes).wp (fun s => s=initial)
  have h6 : Preserves (fun w : World => view w.wg=initial) (Leanux.Env.Stack.receive6 bytes) := (product_store_view (stackReceive6_sameKernel bytes)).wp (fun s => s=initial)
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => view w.wg=initial) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  rxstack_preserves_source [Leanux.Env.deliverInner,Leanux.Env.Stack.receive,invariant]
    using [h4,h6,ambient]

/-- The actual Stack callback retains both fields, including the path that
re-enters native transmit. No peer-residency premise is needed. -/
theorem stack_view (packets : List (List UInt8)) :
    SameView (fun w : World => view w.wg) (packets.forM Leanux.Env.deliverInner) := by
  induction packets with
  | nil => exact SameView.pure _ _
  | cons bytes rest ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact (deliverInner_view bytes).bind (fun _ => ih)

private theorem peek_structure (pid : PeerId) : SameView view (peekRxQueue pid) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold peekRxQueue
  repeat' first
    | (rx_retention_head PrevQueue.peek; exact (store_view (prevQueuePeek_sameWGStore _)).wp (fun s => s=initial))
    | base_rx_step initial

private theorem drop_structure (pid : PeerId) : SameView view (dropRxQueue pid) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold dropRxQueue
  repeat' base_rx_step initial

private theorem complete_structure (pid : PeerId) : SameView view (completeRxQueue pid) := by
  intro initial
  change Preserves (fun w => view w=initial) _
  unfold completeRxQueue
  repeat' base_rx_step initial

/-- The callback keeps its arbitrary product domain and explicit exact-view
contract. The original poll retains all budget and recorded-branch Stops. -/
theorem poll_view (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, SameView (fun w : World => view w.wg) (callback xs)) :
    SameView (fun w : World => view w.wg) (rxPoll pid budget callback) := by
  intro initial
  change Preserves (fun w : World => view w.wg=initial) _
  rw [← rxPollGrouped_eq]
  unfold rxPollGrouped
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch,invariant,unsupported,WG.andM]
  repeat' first
    | (rx_retention_head napiGroReceive
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groReceive_preserves)
         _ callback (fun xs => (hc xs).wp (fun s => s=initial)) _ _)
    | (rx_retention_head napiGroFlushAll
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groFlush_preserves)
         _ callback (fun xs => (hc xs).wp (fun s => s=initial)) _)
    | (allocation_release_lift_from WG.M
       apply PublicationPoll.native_product (fun w => view w=initial)
       simp only [monadLift_self]
       repeat' first
         | (rx_retention_head peekRxQueue; exact (peek_structure _).wp (fun s => s=initial))
         | (rx_retention_head dropRxQueue; exact (drop_structure _).wp (fun s => s=initial))
         | (rx_retention_head completeRxQueue; exact (complete_structure _).wp (fun s => s=initial))
         | (rx_retention_head counterValidate; exact (counterValidate_view _ _).wp (fun s => s=initial))
         | (rx_retention_head consumeDataDone; exact (consumeDataDone_view _ _ _).wp (fun s => s=initial))
         | (rx_retention_head endpointFromSkb; exact (store_view (endpointFromSkb_sameWGStore _)).wp (fun s => s=initial))
         | base_rx_step initial)
    | (allocation_release_lift_from AmbientM; exact productAmbient_spec _ _ (fun _ _ hi => hi))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World => view w.wg=initial)
       intro x b
       change Preserves (fun w : World => view w.wg=initial) _)
    | rx_retention_step

theorem poll_stack_view (pid : PeerId) (budget : Nat) :
    SameView (fun w : World => view w.wg)
      (rxPoll pid budget (fun packets => packets.forM Leanux.Env.deliverInner)) :=
  poll_view pid budget _ stack_view

end Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
