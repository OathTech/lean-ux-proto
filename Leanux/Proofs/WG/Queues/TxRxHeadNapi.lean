import Leanux.Proofs.WG.Queues.TxRxHeadPoll

/-! The original saved NAPI scans and concrete Stack polls preserve the old
TX head on normal return. Their actual observed Stop prefixes remain appended;
no stopped endpoint is asserted. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.RxHeadNapi
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem product_transport (target : SkbId) (state : PacketState)
    (same : productStoreView v = productStoreView w)
    (hi : StackHead.Inv target state w.wg) : StackHead.Inv target state v.wg := by
  have eq := congrArg (fun s : ProductStore43 => s.2.2.2) same
  change wgStoreView v.wg = wgStoreView w.wg at eq
  have hd := congrArg WGStoreView.dev eq
  change v.wg.dev = w.wg.dev at hd
  obtain ⟨h,ha⟩ := hi.1
  exact ⟨⟨h,ha.store eq⟩,by simpa only [HeadState,txPackets,hd] using hi.2⟩

private theorem observed {E α : Type} (target : SkbId) (state : PacketState)
    (g : PrefixM E α) (a : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g a)
    (keeps : Preserves (fun w : World => StackHead.Inv target state w.wg) a) :
    PrefixPreserves (fun _ w => StackHead.Inv target state w.wg) (fun _ => True) g := by
  intro w h hi
  obtain ⟨suffix,history⟩ := appends w h
  refine ⟨suffix,history,True.intro,?_⟩
  cases run : (runPrefix g w h).1 with
  | error e => trivial
  | ok out => exact (hoare_iff_run _ _ _).mp keeps w out.1 out.2 hi ((erases w h).symm.trans run)

private theorem pending_observed (target : SkbId) (state : PacketState) :
    PrefixPreserves (fun _ w => StackHead.Inv target state w.wg) (fun _ => True)
      (RxHistory.mixed (liftWGObserver RxNapi.pendingPrefix)) := by
  apply observed target state _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.pending_erases))
  apply PublicationPoll.native_product (StackHead.Inv target state)
  unfold RxNapi.pendingSource
  exact preserves_bind
    ((pinned_const _private.Leanux.Proofs.WG.Queues.TxStackHead.«0».Leanux.Proofs.WG.Queues.TxDisposition.StackHead.native_store)
      target state _ getDev_sameWGStore)
    (fun _ => preserves_pure _)

private theorem scheduled_observed (target : SkbId) (state : PacketState) :
    PrefixPreserves (fun _ w => StackHead.Inv target state w.wg) (fun _ => True)
      (RxHistory.mixed (liftWGObserver RxNapi.scheduledPrefix)) := by
  apply observed target state _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.scheduled_erases))
  apply PublicationPoll.native_product (StackHead.Inv target state)
  unfold RxNapi.scheduledSource
  exact preserves_bind
    ((pinned_const _private.Leanux.Proofs.WG.Queues.TxStackHead.«0».Leanux.Proofs.WG.Queues.TxDisposition.StackHead.native_store)
      target state _ getDev_sameWGStore)
    (fun _ => preserves_pure _)

theorem poll_observed (target : SkbId) (state : PacketState) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun _ w => StackHead.Inv target state w.wg) (fun _ => True)
      (RxHistory.observePoll pid budget) :=
  observed target state _ _ (RxHistory.observePoll_appends pid budget)
    (RxHistory.observePoll_erases pid budget) (RxHeadPoll.stack pid budget target state)

theorem softirq_observed (target : SkbId) (state : PacketState) :
    PrefixPreserves (fun _ w => StackHead.Inv target state w.wg) (fun _ => True) RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport target state eq hi)
    (pending_observed target state) (poll_observed target state)

theorem inline_observed (target : SkbId) (state : PacketState) :
    PrefixPreserves (fun _ w => StackHead.Inv target state w.wg) (fun _ => True) RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport target state eq hi)
    (pending_observed target state) (poll_observed target state)

theorem irqExit_observed (target : SkbId) (state : PacketState) :
    PrefixPreserves (fun _ w => StackHead.Inv target state w.wg) (fun _ => True) RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves (fun _ _ _ => True.intro) (fun _ _ _ eq hi => product_transport target state eq hi)
    (scheduled_observed target state) (softirq_observed target state)

private theorem native {α : Type} (target : SkbId) (state : PacketState)
    (g : RxHistory.Obs α) (a : Leanux.M α) (erases : ErasesPrefix g a)
    (keep : PrefixPreserves (fun _ w => StackHead.Inv target state w.wg) (fun _ => True) g) :
    Preserves (fun w : World => StackHead.Inv target state w.wg) a := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  have actual := (erases w []).trans run
  have post := (keep w [] hi).choose_spec.2.2
  rw [actual] at post
  exact post

theorem softirq (target : SkbId) (state : PacketState) :
    Preserves (fun w : World => StackHead.Inv target state w.wg) Env.napiSoftirq :=
  native target state _ _ RxHistory.napiSoftirq_erases (softirq_observed target state)

theorem inline (target : SkbId) (state : PacketState) :
    Preserves (fun w : World => StackHead.Inv target state w.wg) Env.pollScheduledInline :=
  native target state _ _ RxHistory.pollScheduledInline_erases (inline_observed target state)

theorem irqExit (target : SkbId) (state : PacketState) :
    Preserves (fun w : World => StackHead.Inv target state w.wg) Env.napiIrqExit :=
  native target state _ _ RxHistory.napiIrqExit_erases (irqExit_observed target state)

end Leanux.Proofs.WG.Queues.TxDisposition.RxHeadNapi
