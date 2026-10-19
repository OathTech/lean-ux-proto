import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPeerReleaseFrames

/-! Publication's actual observed repayment emits a valid nonfinal receipt.
The source-derived extra reference rules out staged disposal at that cut;
this statement does not infer an internal event from endpoint erasure alone. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Publication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open HandshakeSecurity.StagedDisposal
set_option pp.structureInstances false

theorem observed_borrow_funded (items : List SkbId)
    (performed : runPrefix (borrow items) w history = (.ok ((first,pid),v),last)) :
    ∃ n, 1 < n ∧ (PeerBorrow.resident (wgStoreView v.wg) pid).map (·.refcount) = some n := by
  have full := (borrow_erases items w history).symm.trans (congrArg Prod.fst performed)
  rw [liftWG_run] at full
  cases native : ((borrowNative items).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at full
  | ok out =>
    obtain ⟨⟨value,g⟩,ambient⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨rfl,rfl,rfl⟩ := full
    exact borrow_funded items w.ambient ambient native

theorem observed_middle_funded (pid : PeerId) (first : SkbId) (state : PacketState)
    (funded : ∃ n, 1 < n ∧ (PeerBorrow.resident (wgStoreView w.wg) pid).map (·.refcount) = some n)
    (performed : runPrefix (middle pid first state) w history = (.ok ((),v),last)) :
    ∃ n, 1 < n ∧ (PeerBorrow.resident (wgStoreView v.wg) pid).map (·.refcount) = some n := by
  have full := (middle_erases pid first state w history).symm.trans (congrArg Prod.fst performed)
  rw [liftWG_run] at full
  cases native : ((TxDisposition.publicationMiddle pid first state).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at full
  | ok out =>
    obtain ⟨⟨ignored,g⟩,ambient⟩ := out
    cases ignored
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨_,rfl⟩ := full
    exact middle_funded pid first state funded w.ambient ambient native

/-- At the actual reached publication repayment, the counted receipt is
nonfinal and the callback completes. The receipt position includes all
preceding peer accesses; no fabricated or history-reset receipt is used. -/
theorem repayment_nonfinal (pid : PeerId)
    (funded : ∃ n, 1 < n ∧ (PeerBorrow.resident (wgStoreView w.wg) pid).map (·.refcount) = some n)
    (history : List CausalJournal.Event) :
    ∃ g ambient cutHistory,
      runWGPrefix (PeerRelease.cut (some pid)) w.wg w.ambient history =
        (.ok ((none,g),ambient),cutHistory) ∧
      runPrefix (Admission.actualOps.release (some pid)) w history =
        (.ok ((),{w with wg := g,ambient := ambient}),
          cutHistory ++ [PeerRelease.receipt (some pid) none w.wg g w.ambient ambient]) ∧
      (⟨none,w.wg,g,w.ambient,ambient⟩ : WGRunWitness (Option (PeerId × Peer))).Valid (releaseCut (some pid)) ∧
      (Event.release (some pid) ⟨none,w.wg,g,w.ambient,ambient⟩).arm = none := by
  obtain ⟨g,ambient,native⟩ := release_cut_nonfinal pid funded w.ambient
  have erased := PeerRelease.cut_erases (some pid) w.wg w.ambient history
  change (runWGPrefix (PeerRelease.cut (some pid)) w.wg w.ambient history).1 = _ at erased
  have source : runWGPrefix (PeerRelease.cut (some pid)) w.wg w.ambient history =
      (.ok ((none,g),ambient),
        (runWGPrefix (PeerRelease.cut (some pid)) w.wg w.ambient history).2) :=
    Prod.ext (erased.trans native) rfl
  refine ⟨g,ambient,_,source,?_,native,rfl⟩
  rw [PeerRelease.after_cut (some pid) source]
  rfl

/-- The actual earlier borrow and middle executions discharge the funding
condition for the reached publication repayment on the same source chain. -/
theorem source_repayment_nonfinal (items : List SkbId) (state : PacketState)
    (acquired : runPrefix (borrow items) w history = (.ok ((first,pid),u),borrowHistory))
    (published : runPrefix (middle pid first state) u borrowHistory = (.ok ((),v),publishedHistory)) :
    ∃ g ambient cutHistory,
      runPrefix (Admission.actualOps.release (some pid)) v publishedHistory =
        (.ok ((),{v with wg := g,ambient := ambient}),
          cutHistory ++ [PeerRelease.receipt (some pid) none v.wg g v.ambient ambient]) ∧
      (⟨none,v.wg,g,v.ambient,ambient⟩ : WGRunWitness (Option (PeerId × Peer))).Valid (releaseCut (some pid)) := by
  have funded := observed_middle_funded pid first state (observed_borrow_funded items acquired) published
  obtain ⟨g,ambient,cutHistory,_,run,valid,_⟩ := repayment_nonfinal pid funded publishedHistory
  exact ⟨g,ambient,cutHistory,run,valid⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Publication
