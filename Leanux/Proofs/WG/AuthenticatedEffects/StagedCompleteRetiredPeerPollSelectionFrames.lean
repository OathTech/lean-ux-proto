import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollSelection

/-! The unchanged poll observer selects its real cached head and appends the
one removal occurrence. That actual suffix fixes the remaining carrier list. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Poll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders RxJoint PollCarrier

theorem Context.store (account : Context front initial loans h w)
    (same : wgStoreView v.wg = wgStoreView w.wg)
    (history : removedPackets k = removedPackets h) : Context front initial loans k v := by
  obtain ⟨holders,account,stable⟩ := account
  refine ⟨holders,?_,?_⟩
  · change Phased _ (front ++ remaining initial _) loans v.wg
    rw [history]
    exact account.store same
  · change StableRx (remaining initial _) v.wg
    rw [history]
    exact stable.kernel same

theorem peek (initial : RxCredits.Ledger) (loans : Reservations) (pid : PeerId) :
    PrefixEnsures (Boundary initial loans) (fun _ => True)
      (access (liftWGObserver (peekAccess pid))) (AfterPeek initial loans pid) := by
  apply PollCarrier.normal_spec (access_appends _)
  intro w h first v before run
  obtain ⟨holders,account⟩ := before.exact
  have original := (access_erases (liftWGObserver_erases (peekAccess_erases pid)) w h).symm.trans run
  have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
    _ w v first original
  obtain ⟨after,selected⟩ := account.rx_peek pid w.ambient v.ambient native
  have history := removed_frame (access_removed (liftWGObserver (peekAccess pid))) w h
  refine ⟨⟨holders,?_,?_⟩,selected,peek_head pid w.wg v.wg first w.ambient v.ambient native⟩
  · change Phased _ ([] ++ remaining initial _) loans v.wg
    rw [history]
    exact after.phased
  · change StableRx (remaining initial _) v.wg
    rw [history]
    exact after.stable

theorem ready (initial : RxCredits.Ledger) (loans : Reservations) (pid : PeerId) (first : Option SkbId) :
    PrefixEnsures (AfterPeek initial loans pid first) (fun _ => True)
      (access (liftWGObserver (readyAccess first))) (Checked initial loans pid first) := by
  apply PollCarrier.normal_spec (access_appends _)
  intro w h go v before run
  obtain ⟨holders,account⟩ := before.1.exact
  have old := (stable_ready_observed initial (holders.owners ++ loans) pid first w h
    ⟨⟨account.funded.carriers,before.2.1⟩,account.stable,before.2.2⟩).choose_spec.2.2
  rw [run] at old
  have original := (access_erases (liftWGObserver_erases (readyAccess_erases first)) w h).symm.trans run
  have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
    _ w v go original
  have same := (ready_result first w.wg v.wg go w.ambient v.ambient native).1
  exact ⟨before.1.store (congrArg wgStoreView same)
    (removed_frame (access_removed (liftWGObserver (readyAccess first))) w h),old.1.2,old.2.2⟩

theorem capture (initial : RxCredits.Ledger) (loans : Reservations) (pid skb : Nat) :
    PrefixEnsures (Checked initial loans pid (some skb) true) (fun _ => True)
      (RxJoint.capture skb) (Captured initial loans pid skb) := by
  apply PollCarrier.normal_spec (capture_appends skb)
  intro w h out v before run
  obtain ⟨holders,account⟩ := before.1.exact
  have old := (stable_capture_observed initial (holders.owners ++ loans) pid skb w h
    ⟨⟨account.funded.carriers,before.2.1⟩,account.stable,before.2.2.2 rfl⟩).choose_spec.2.2
  rw [run] at old
  have same := (RxDisposition.capture_selected skb w v h out.1 out.2 run).1
  have quiet : HistoryFrame removedStamp (RxJoint.capture skb) := by
    intro w h
    rw [capture_run]
    cases (liftWG (getRxSkb skb)).run w <;> simp [removedStamp,List.filterMap_append]
  exact ⟨before.1.store (congrArg (fun s : World => wgStoreView s.wg) same)
    (removed_frame quiet w h),old.1.1.2,old.1.2,old.2.2⟩

theorem drop (initial : RxCredits.Ledger) (loans : Reservations) (pid n skb : Nat)
    (stamp : PacketStamp) (pkt : RxPacket) :
    PrefixEnsures (Captured initial loans pid skb (pkt,stamp)) (fun _ => True)
      (RxJoint.drop pid n skb stamp) (fun _ => Live initial loans pid skb stamp pkt) := by
  apply PollCarrier.normal_spec ((access_appends _).bind (fun _ => emit_appends _))
  intro w h out v before run
  obtain ⟨holders,account⟩ := before.1.exact
  simp only [runPrefix_bind] at run ⊢
  cases accessRun : runPrefix (access (liftWGObserver (rxDropPeekedPrefix pid))) w h with
  | mk result journal =>
    cases result with
    | error e => simp [accessRun] at run
    | ok result =>
      obtain ⟨u,after⟩ := result
      cases u
      simp only [accessRun,runPrefix_emit,Except.ok.injEq,Prod.mk.injEq] at run
      have eq := run.2
      subst after
      simp only [runPrefix_emit]
      obtain ⟨d,p,device,peer,peeked⟩ := before.2.1
      have stampEq : stamp = (d.ifindex,skb+1) := by
        simpa [Lifetimes.packetStamp,device] using before.2.2.1.1.symm
      have cell : d.rxSkbs[skb]? = some pkt := by
        simpa [RxDisposition.rxStore,RxDisposition.nativeRxStore,device] using before.2.2.1.2
      have original : (liftWG (dropRxQueue pid)).run w = .ok ((),v) :=
        (access_erases (liftWGObserver_erases (rxDropPeekedPrefix_erases pid)) w h).symm.trans
          (congrArg Prod.fst accessRun)
      have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
        _ w v () original
      obtain ⟨kept,stable⟩ := account.rx_select device peer peeked cell before.2.2.2 w.ambient v.ambient native
      have quiet : removedPackets journal = removedPackets h := by
        simpa only [accessRun] using removed_frame (access_removed (liftWGObserver (rxDropPeekedPrefix pid))) w h
      have removed : removedPackets (journal ++ [RxJoint.Event.removed n skb stamp]) =
          removedPackets h ++ [⟨d.ifindex,skb⟩] := by
        simpa [removedPackets,removedStamps,List.filterMap_append,removedStamp,stampEq,packetOfStamp] using
          congrArg (fun xs => xs ++ [⟨d.ifindex,skb⟩]) quiet
      refine ⟨⟨⟨d.ifindex,pid,p.internalId⟩,rfl,by simp [stampEq],holders,?_,?_⟩,
        RxDisposition.selected_transport skb stamp pkt w v
          ((ProjectedAction.iff_run _ _ _).mp (RxDisposition.drop_rxStore pid) w () v original) before.2.2.1⟩
      · change Phased _ (_ ++ remaining initial _) loans v.wg
        rw [removed,remaining_append]
        simpa only [Selected,packetOfStamp,stampEq,Nat.add_sub_cancel,List.cons_append,List.nil_append,rest] using kept
      · change StableRx (remaining initial _) v.wg
        rw [removed,remaining_append]
        exact stable

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Poll
