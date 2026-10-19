import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNapiPointSource

/-! Native poll frames retain the actual full packet ledger. The stronger
outer allocation companion is not assumed at every RX intermediate cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity CausalJournal

abbrev Carrier := CompletePoll.Carrier [] []
abbrev Checked (action : PrefixM Event α) := CompletePoll.Checked [] [] CompleteProduct.Safe action

theorem carrier_safe (h : History) (w : World) (before : Carrier h w) : CompleteProduct.Safe h := by
  obtain ⟨ledger,accounted⟩ := before
  exact CompleteProduct.account_safe ledger h w.wg accounted

theorem ambient_checked (action : AmbientM α) : Checked (liftPrefix (liftAmbient action)) :=
  viewLiftPrefix_preserves productStoreView carrier_safe CompleteStack.stable
    (fun initial => productAmbient_spec action (fun w => productStoreView w = initial) (fun _ _ hi => hi))

theorem Native.checked (token : Native action) : Checked action := by
  cases token with
  | ambient =>
    apply viewLiftPrefix_preserves productStoreView carrier_safe CompleteStack.stable
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w value v run
    cases run
    rfl
  | hiddenSite => exact ambient_checked _
  | choose =>
    apply viewLiftPrefix_preserves productStoreView carrier_safe CompleteStack.stable
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w value v run
    cases run
    rfl
  | start => exact ambient_checked _
  | stop => exact ambient_checked _
  | netEnter =>
    apply viewLiftPrefix_preserves productStoreView carrier_safe CompleteStack.stable
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w value v run
    cases run
    rfl
  | netLeave =>
    apply viewLiftPrefix_preserves productStoreView carrier_safe CompleteStack.stable
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w value v run
    cases run
    rfl
  | pending =>
    apply CompletePoll.state _
    apply CompletePassive.native _ CompleteProduct.account_safe
    unfold RxNapi.pendingSource
    exact SameView.bind (TimerFrames.store getDev_sameWGStore) (fun _ => SameView.pure _ _)
  | scheduled =>
    apply CompletePoll.state _
    apply CompletePassive.native _ CompleteProduct.account_safe
    unfold RxNapi.scheduledSource
    exact SameView.bind (TimerFrames.store getDev_sameWGStore) (fun _ => SameView.pure _ _)
  | branch site yes => complete_poll_native CompleteProduct.Safe using CompleteProduct.account_safe
  | peek pid => complete_poll_native CompleteProduct.Safe using CompleteProduct.account_safe
  | install pid queue => complete_poll_native CompleteProduct.Safe using CompleteProduct.account_safe
  | writePeer pid queue scheduled => complete_poll_native CompleteProduct.Safe using CompleteProduct.account_safe
  | ready first => complete_poll_native CompleteProduct.Safe using CompleteProduct.account_safe
  | packet skb => complete_poll_native CompleteProduct.Safe using CompleteProduct.account_safe
  | drop pid => complete_poll_native CompleteProduct.Safe using CompleteProduct.account_safe
  | endpoint source => complete_poll_native CompleteProduct.Safe using CompleteProduct.account_safe
  | keyPut kid => complete_poll_native CompleteProduct.Safe using CompleteProduct.account_safe
  | free skb => exact CompletePoll.state _ (CompletePollNative.free_rx _ CompleteProduct.account_safe skb)
  | complete pid => complete_poll_native CompleteProduct.Safe using CompleteProduct.account_safe
  | candidate skb packet => exact CompletePoll.candidate _ CompleteProduct.account_safe skb packet
  | leave position => exact CompletePoll.leave _ CompleteProduct.account_safe position
  | enter cause =>
    intro w h before
    obtain ⟨ledger,accounted⟩ := before
    have kept := accounted.append_quiet [.scope (.entered ⟨h.length,cause⟩)]
      (by intro event member; simp only [List.mem_singleton] at member; subst event; rfl)
      (by intro event member position; simp only [List.mem_singleton] at member; subst event; rfl)
    exact ⟨[_],rfl,CompleteProduct.account_safe ledger _ _ kept,ledger,kept⟩
  | exit position => exact CompletePoll.emit _ CompleteProduct.account_safe _ rfl (fun _ => rfl)
  | cut => exact ambient_checked _
  | routeOutput src dst =>
    exact viewLiftPrefix_preserves productStoreView carrier_safe CompleteStack.stable
      (liftWG_sameProductStore _ (liftRouting_sameWGStore _))
  | routeInput src dst =>
    exact viewLiftPrefix_preserves productStoreView carrier_safe CompleteStack.stable
      (liftWG_sameProductStore _ (liftRouting_sameWGStore _))
  | neighbour =>
    exact viewLiftPrefix_preserves productStoreView carrier_safe CompleteStack.stable
      (liftWG_sameProductStore _ (liftRouting_sameWGStore _))
  | device =>
    exact viewLiftPrefix_preserves productStoreView carrier_safe CompleteStack.stable
        (fun initial => productGetDev_spec (fun w => w = initial))
  | world =>
    exact viewLiftPrefix_preserves productStoreView carrier_safe CompleteStack.stable
        (fun initial => productGetWG_spec (fun w => w = initial))
  | inbox f =>
    apply viewLiftPrefix_preserves productStoreView carrier_safe CompleteStack.stable
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w value v run
    cases run
    rfl
  | invariant message =>
    exact PrefixEnsures.lift _ carrier_safe (by intro h w value v before run; cases run)
  | unsupported message =>
    exact PrefixEnsures.lift _ carrier_safe (by intro h w value v before run; cases run)
  | excluded message =>
    exact PrefixEnsures.lift _ carrier_safe (by intro h w value v before run; cases run)
  | wgInvariant message => complete_poll_native CompleteProduct.Safe using CompleteProduct.account_safe
  | wgUnsupported message => complete_poll_native CompleteProduct.Safe using CompleteProduct.account_safe

theorem Child.checked (token : Child) : Checked token.action := by
  cases token with
  | counter skb packet => exact CompletePoll.counter _ CompleteProduct.account_safe skb packet
  | consume pid packet endpoint =>
    exact CompletePoll.state _
        (CompleteReceiveConsumer.checked _ CompleteProduct.account_safe pid packet endpoint
          (CompleteProduct.source_state (CompleteTransmit.staging pid)))
  | release peer => exact CompletePoll.state _ (CompleteSource.original peer _ CompleteProduct.account_safe)
  | transmit family addr packets mtu =>
    exact CompletePoll.state _
        (CompleteProduct.source_state (CompleteTransmit.transmit family addr packets mtu))
  | receive6 bytes =>
    exact viewLiftPrefix_preserves productStoreView carrier_safe CompleteStack.stable
        (stackReceive6_sameKernel bytes)

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

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Napi.Points
