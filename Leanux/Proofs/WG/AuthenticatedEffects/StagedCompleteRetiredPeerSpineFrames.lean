import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerSpine

/-! Exact-account frames use equality of C1's actual store projection.
Deletion-retaining holder frames alone cannot justify an upper bound. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders

theorem Account.store (account : Account holders carriers loans w)
    (same : wgStoreView v = wgStoreView w) : Account holders carriers loans v := by
  have device : v.dev = w.dev := congrArg WGStoreView.dev same
  have peers : peerView v = peerView w := by simp only [peerView,device]
  exact ⟨⟨account.funded.aligned.frame (Frame.of_store same),account.funded.carriers.kernel same⟩,
    account.upper.peer_view peers,account.stable.kernel same⟩

theorem ExactBoundary.store (account : ExactBoundary carriers loans w)
    (same : wgStoreView v = wgStoreView w) : ExactBoundary carriers loans v := by
  obtain ⟨holders,account⟩ := account
  exact ⟨holders,account.store same⟩

theorem ExactAt.store (account : ExactAt initial loans before history w)
    (same : productStoreView v = productStoreView w) : ExactAt initial loans before history v := by
  obtain ⟨suffix,history,account⟩ := account
  exact ⟨suffix,history,account.store (congrArg (fun p : ProductStore43 => p.2.2.2) same)⟩

/-- A source callback may add audit events but cannot erase an RX carrier
without the matching removal event. The resulting holder witness is retained. -/
theorem ExactAt.frame (action : RxHistory.Obs α) (original : Leanux.M β) (project : α → β)
    (appends : Appends action) (erase : ErasesTo project action original)
    (same : SameProductStore original)
    (quiet : ∀ w h, NapiCarrier.removedPackets (runPrefix action w h).2 = NapiCarrier.removedPackets h) :
    PrefixPreserves (ExactAt initial loans before) (fun _ => True) action := by
  apply NapiCarrier.normal_spec appends
  intro w h x v account actual
  obtain ⟨old,history,account⟩ := account
  obtain ⟨extra,extended⟩ := appends w h
  have empty : NapiCarrier.removedPackets extra = [] := by
    have eq := quiet w h
    rw [extended] at eq
    exact List.append_cancel_left (by
      simpa only [NapiCarrier.removedPackets,List.filterMap_append,List.append_nil] using eq)
  have run : original.run w = .ok (project x,v) := by rw [←erase w h,actual]; rfl
  have kept := ExactAt.store (initial := initial) (loans := loans) (before := before)
    ⟨old,history,account⟩ ((ProjectedAction.iff_run _ _ _).mp same w (project x) v run)
  obtain ⟨old',history',account'⟩ := kept
  refine ⟨old' ++ extra,by rw [extended,history',List.append_assoc],?_⟩
  simp only [NapiCarrier.removedPackets,List.filterMap_append]
  change ExactBoundary
    (remaining initial (NapiCarrier.removedPackets old' ++ NapiCarrier.removedPackets extra)) loans v.wg
  rw [empty,List.append_nil]
  exact account'

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
