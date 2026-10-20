import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedXmitConcreteSource

/-! Fixture and descriptor bookkeeping retain the routed child's account.
No callback account is supplied by the caller's source-point witness. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.XmitConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Configuration TransmitSecurity CausalJournal
abbrev Account := Lifecycle.Points.Account

theorem leading_checked (input : Input) : CompleteProduct.Checked (leading input) := by
  unfold leading Xmit.callPrefix
  apply PrefixPreserves.bind (CompleteProduct.fs (fdget SENDER_FD))
  intro fd
  split
  · exact PrefixPreserves.pure CompleteProduct.carrier_safe _
  · apply PrefixPreserves.bind (Xmit.prepare_checked input.family input.address input.payload input.options)
    intro prepared
    cases prepared with
    | routeRefused err | packetsRefused err=>exact PrefixPreserves.pure CompleteProduct.carrier_safe _
    | ready packets mtu=>
      exact PrefixPreserves.bind (Xmit.entered_checked input.family input.address packets mtu)
        (fun _=>PrefixPreserves.pure CompleteProduct.carrier_safe _)

theorem leave_normal (before : Account h w)
    (performed : runPrefix (leave token) w h=(.ok ((),u),middle)) : Account middle u := by
  change (Except.ok ((),w),h++[Event.scope (.exited token)])=(.ok ((),u),middle) at performed
  simp only [Prod.mk.injEq,Except.ok.injEq] at performed
  obtain ⟨⟨_,rfl⟩,rfl⟩:=performed
  obtain ⟨ledger,account⟩:=before
  exact ⟨ledger,account.append_quiet [.scope (.exited token)]
    (by intro event member; cases List.mem_singleton.mp member; rfl)
    (by intro event member; cases List.mem_singleton.mp member; intro position; rfl)⟩

theorem put_normal (before : Account h w)
    (performed : runPrefix (put fd) w h=(.ok ((),u),middle)) : Account middle u := by
  rw [put,runPrefix_lift] at performed
  have history : middle=h := (congrArg Prod.snd performed).symm
  subst middle
  have frame : Preserves (Account h) (liftFS (fdput fd)) :=
    productFS_spec (fdput fd) _ (fun _ _ _ _ before=>before)
  exact (hoare_iff_run _ _ _).mp frame _ _ _ before (congrArg Prod.fst performed)

variable {Good : History → World → Prop}

/-- Security: the direct transmit dispatch retains the routed packet account
through fixture exit and descriptor repayment. Its original refusal paths and
continuation remain intact; deeper preparation/front atoms stay explicit. -/
theorem Point.safe
    (accountGood : ∀h w,Account h w → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (before : CompleteProduct.Carrier h w) (point : Point input w h u middle) : Good middle u := by
  cases point with
  | entry=>exact accountGood _ _ before.1
  | leading performed=>exact accountGood _ _ (Xmit.normal (leading_checked input) before performed).1
  | routed path point=>exact point.safe accountGood acceptStaging acceptPeer (path.entry before).1
  | bodyReturned path performed=>exact accountGood _ _ (RoutedTransmit.normal (path.entry before).1 performed)
  | scopeLeft path performed left=>
      exact accountGood _ _ (leave_normal (RoutedTransmit.normal (path.entry before).1 performed) left)
  | descriptorPut path performed left paid=>
      exact accountGood _ _ (put_normal (leave_normal (RoutedTransmit.normal (path.entry before).1 performed) left) paid)
  | returned performed=>
      exact accountGood _ _
        (Xmit.normal (CompleteProduct.Traffic.syscallXmit input.family input.address input.payload input.options) before performed).1

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.XmitConcrete
