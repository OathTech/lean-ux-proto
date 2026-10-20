import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumeLeafPointSource

/-! Actual native frames retain RX allocation bounds as well as staged/TX
ownership. A successful lookup's acquired peer is its own source result. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity CausalJournal

abbrev Carrier := Points.Carrier
abbrev Checked (action : PrefixM Event α) := Points.Checked action

theorem carrier_safe (h : History) (w : World) (before : Carrier h w) : CompleteProduct.Safe h :=
  Points.carrier_safe h w before

theorem native_checked (action : WG.M α) (frame : SameView StagedEntry.view action) : Checked (wg action) :=
  Points.native_checked action frame

theorem aip_read (body : AipM α) (frame : SameView id body) : SameView StagedEntry.view (liftAip body) := by
  apply TimerFrames.store
  intro initial
  apply hoare_liftAip_of body (fun w => wgStoreView w = initial) (fun _ w => wgStoreView w = initial)
  intro g d hg hd
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro s ambient x s' ambient' hs hr
  have he := (ProjectedAction.iff_run_ambient _ _ _).mp frame s ambient x s' ambient' hr
  change s' = s at he
  rw [he,hs]
  simpa [wgStoreView,hd] using hg

theorem acquire_frame (peer : Option PeerId) : SameView StagedEntry.view (peerGetMaybeZero peer) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have borrowed := ((hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.acquire_spec peer (wgStoreView w)) w a result v b rfl run).2
  cases result with
  | none =>
    change wgStoreView v = wgStoreView w at borrowed
    have same : v.dev = w.dev := congrArg WGStoreView.dev borrowed
    change StagedEntry.view {dev := v.dev} = StagedEntry.view {dev := w.dev}
    rw [same]
  | some pid =>
    obtain ⟨d,p,device,resident,_,after⟩ := borrowed
    change w.dev = some d at device
    have same := congrArg WGStoreView.dev after
    change v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount+1}} at same
    change StagedEntry.view {dev := v.dev} = _
    rw [same]
    exact Queued.replace_peer device resident (q := {p with refcount := p.refcount+1}) rfl rfl rfl

theorem BaseNative.checked (token : BaseNative action) : Checked action := by
  cases token with
  | basic token => exact token.checked
  | ambient body => exact native_checked _ (fun initial => hoare_liftAmbient body (fun w => StagedEntry.view w = initial))
  | world =>
    apply native_checked
    intro initial
    exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  | device => exact native_checked _ (TimerFrames.store getDev_sameWGStore)
  | update pid f fields => exact native_checked _ (Queued.update pid f fields)
  | dereference owner =>
    apply native_checked
    intro initial
    exact indexOwner_peerDeref_preserves _ _
  | unhash owner => exact native_checked _ (KeyFrames.index _)
  | eraseKey kid => exact native_checked _ (ReceiveFrames.device _
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
  | endian bits => exact native_checked _ (TimerFrames.store (swapEndian_sameWGStore bits))

theorem Native.checked (token : Native) : Checked token.action := by
  cases token with
  | metadata body source => exact native_checked _ source.frame
  | base token => exact token.checked
  | find root bits key => exact native_checked _ (aip_read _ (findNode_sameAipStore root bits key))
  | node id => exact native_checked _ (aip_read _ (getNode_sameAipStore id))
  | acquire peer => exact native_checked _ (acquire_frame peer)
  | change f same => exact native_checked _ (KeyFrames.world f same)
  | failure reason =>
    apply native_checked
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a value v b run
    cases run
  | history =>
    intro w h before
    exact ⟨[],by simp only [List.append_nil]; rfl,carrier_safe h w before,before⟩
  | armed receipt =>
    exact CompletePoll.state _ (CompletePassive.emit _ CompleteProduct.account_safe (.armed receipt) rfl (fun _ => rfl))

theorem Child.checked (token : Child) : Checked token.action := by
  cases token with
  | wheel pid timer expires clock unit =>
    apply native_checked
    exact TimerFrames.combine
      (PacketOrigins.epoch_ring ((RetirementSecurity.placeOnWheel_cryptWire pid timer expires clock unit).factor Prod.fst))
      (Staged.Exact.place pid timer expires clock unit)
      (AllocatedObligation.CompletionGeometry.placeOnWheel_geometry pid timer expires clock unit)
      (RetirementSecurity.contents_factor (RetirementSecurity.ownership_queues
        (RetirementSecurity.placeOnWheel_ownership pid timer expires clock unit)))
  | arm pid timer delay clock =>
    exact CompletePoll.state _ (CompleteTimer.arm _ CompleteProduct.account_safe pid timer delay clock)

theorem Shape.checked (shape : Shape action) : Checked action := by
  induction shape with
  | pure value => exact CompletePoll.pure_checked _ CompleteProduct.account_safe value
  | native token => exact token.checked
  | child token => exact token.checked
  | failed failure next =>
    intro w h before
    obtain ⟨reason,run⟩ := failure.run w h
    exact ⟨[],by simp only [runPrefix_bind,run,List.append_nil],by simpa only [runPrefix_bind,run] using carrier_safe h w before,by simp only [runPrefix_bind,run]⟩
  | bind head tail ihHead ihTail => exact CompletePoll.bind_checked _ ihHead ihTail
  | marked label shape ih => exact ih

theorem Shape.normal (shape : Shape action) (before : Carrier h w)
    (performed : runPrefix action w h = (.ok (value,u),middle)) : Carrier middle u := by
  obtain ⟨suffix,extended,safe,kept⟩ := shape.checked w h before
  rw [performed] at kept
  exact kept

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
