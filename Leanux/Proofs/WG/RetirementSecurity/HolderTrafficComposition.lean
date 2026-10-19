import Leanux.Proofs.WG.RetirementSecurity.HolderTrafficKeys

/-! The original traffic combinators retain exact key credit while admission
changes only the source-selected peer ledger. All scheduler callbacks are
concrete; no invariant of an arbitrary replacement driver is assumed. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem extra_wg_store (entry : Extra temporary locals active w)
    (same : wgStoreView v.wg=wgStoreView w.wg) : Extra temporary locals active v := by
  have device : v.wg.dev=w.wg.dev := congrArg WGStoreView.dev same
  exact ⟨HolderPoll.keys_store entry.1 same,OccurrenceStack.ready_store same entry.2.1,
    BaseCoherence.transport entry.2.2.1 (by simp only [BaseCoherence.view,BaseCoherence.slots,BaseCoherence.rows,device]),
    KeySlotLiveness.store_transport same entry.2.2.2⟩

theorem wg_store (entry : Inv initial loans before temporary locals active h w)
    (same : wgStoreView v.wg=wgStoreView w.wg) : Inv initial loans before temporary locals active h v := by
  have device : v.wg.dev=w.wg.dev := congrArg WGStoreView.dev same
  obtain ⟨suffix,history,account⟩ := entry.1.1.1
  refine ⟨⟨⟨⟨suffix,history,HolderInitial.store account same⟩,?_⟩,
    OwnerControlCalls.store h w v same entry.1.2.1,?_⟩,extra_wg_store entry.2 same⟩
  · simpa only [DecryptIteration.Physical,NativeRxInv,RxRing.nativeCell,device] using entry.1.1.2
  · apply CurrentSlots.fields_transport entry.1.2.2
    unfold CurrentSlots.fields RxCredits.keyWords
    rw [device]

theorem dynamic_wg_store (entry : Dynamic loans temporary locals active h w)
    (same : wgStoreView v.wg=wgStoreView w.wg) : Dynamic loans temporary locals active h v :=
  ⟨_,wg_store entry.choose_spec same⟩

theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe
    (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ := HolderXmit.mixed initial loans before family addr packets mtu w h entry.1
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post
    have source := (RxHistory.mixed_erases (liftWGObserver_erases (wgXmitPrefix_erases family addr packets mtu)) w h).symm.trans run
    have native := HolderPoll.native_receipt source
    exact ⟨post,entry.2.1.transmit entry.2.2.1.1.bounded (CurrentSlots.current entry.1.2.2).compatible
        family addr packets mtu w.ambient out.2.ambient native,
      (hoare_iff_run _ _ _).mp (OccurrenceStack.transmit family addr packets mtu) w out.1 out.2 entry.2.2.1 source,
      BaseCoherence.transport entry.2.2.2.1 ((ProjectedAction.iff_run_ambient _ _ _).mp
        (BaseCoherence.wgXmit_view family addr packets mtu) w.wg w.ambient out.1 out.2.wg out.2.ambient native),
      (hoare_iff_run _ _ _).mp (KeySlotLiveness.transmit (pending:=[]) family addr packets mtu)
        w out.1 out.2 entry.2.2.2.2 source⟩

theorem multicast (family addr : Nat) : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe
    (RxHistory.audit (xmitMulticastLoopAudit family addr)) :=
  join_native (BatchAccount.multicast initial loans before family addr)
    (RxHistory.audit_erases (xmitMulticastLoopAudit_erases family addr))
    (extra_product ((pinned_const _private.Leanux.Proofs.WG.Queues.BatchAccount.«0».Leanux.Proofs.WG.Queues.RxCredits.BatchAccount.multicast_store) family addr))

theorem batch_item (d : Device) (cqes : List Int) (item : BatchItem) : PrefixPreserves
    (Dynamic loans temporary locals active) OwnerChecks.Safe (RxHistory.batchItem d cqes item) := by
  rw [rxBatchItem_factor]
  exact batchItemWith_preserves (fun _ _ entry=>dynamic_safe entry)
    (fun _ _ _ same entry=>dynamic_wg_store entry same) _ _ _ _ receive_dynamic
    (dynamic_fixed (fun _ _=>inline_poll)) (fun family addr=>dynamic_fixed (fun _ _=>multicast family addr))
    (fun family addr packets mtu=>dynamic_fixed (fun _ _=>transmit family addr packets mtu)) d cqes item

theorem batch_loop (d : Device) (items : List BatchItem) (cqes : List Int) : PrefixPreserves
    (Dynamic loans temporary locals active) OwnerChecks.Safe (BatchAccount.loop d items cqes) := by
  unfold BatchAccount.loop
  apply PrefixPreserves.forIn
  · exact fun _ _ entry=>dynamic_safe entry
  · intro item qs
    exact batch_item d qs item

theorem receive_section (msg : List UInt8) (src : SkbSource) : PrefixPreserves
    (Dynamic loans temporary locals active) OwnerChecks.Safe (FloodSection.action msg src) := by
  unfold FloodSection.action
  apply runWorkerPrefix_preserves (fun _ _ entry=>dynamic_safe entry)
    (fun _ _ _ same entry=>dynamic_store entry same)
  exact PrefixPreserves.bind (receive_dynamic msg src) (fun _=>dynamic_fixed (fun _ _=>inline_poll))

theorem flood_route (family : Nat) (src : SkbSource) : PrefixPreserves
    (Dynamic loans temporary locals active) OwnerChecks.Safe (FloodLoop.route family src) := by
  have safe : ∀ h w,Dynamic loans temporary locals active h w→OwnerChecks.Safe h := fun _ _ entry=>dynamic_safe entry
  have store : ∀h w v,productStoreView v=productStoreView w→Dynamic loans temporary locals active h w→Dynamic loans temporary locals active h v :=
    fun _ _ _ same entry=>dynamic_store entry same
  unfold FloodLoop.route
  repeat' traffic_preserve_source safe using store

theorem flood_loop (family : Nat) (src : SkbSource) (messages : List (List UInt8)) : PrefixPreserves
    (Dynamic loans temporary locals active) OwnerChecks.Safe (FloodLoop.loop family src messages) := by
  induction messages with
  | nil=>exact PrefixPreserves.pure (fun _ _ entry=>dynamic_safe entry) _
  | cons msg messages ih=>
    rw [FloodLoop.loop_cons]
    exact PrefixPreserves.bind (PrefixPreserves.bind (flood_route family src) (fun _=>receive_section msg src)) (fun _=>ih)

end Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
