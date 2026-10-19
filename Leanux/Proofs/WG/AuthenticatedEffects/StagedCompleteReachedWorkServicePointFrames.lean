import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkServicePointSource

/-! Native work bookkeeping retains the same packet-account projection.
Counted release remains a separate actual callback and can change the ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity CausalJournal

theorem Native.checked (token : Native) : Checked token.action := by
  cases token with
  | ambient body =>
    apply PrefixEnsures.lift _ Consume.Leaf.carrier_safe
    intro h w value v before run
    have same : v.wg = w.wg := (ProjectedAction.iff_run _ _ _).mp
      (show SameView World.wg (Leanux.liftAmbient body) from fun initial =>
        productAmbient_spec body _ (fun _ _ hi => hi)) w value v run
    obtain ⟨ledger,before⟩ := before
    exact ⟨ledger,by simpa only [same] using before⟩
  | change f same =>
    apply Consume.Leaf.native_checked
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a value v b run
    cases run
    exact same w
  | acquire pid => exact Consume.Leaf.native_checked _ (Queued.acquire pid)
  | expired site birth limit test =>
    exact Consume.Leaf.native_checked _
      ((branchExpired_sameWGWorld site birth limit test).factor StagedEntry.view)
  | queued receipt =>
    exact CompletePoll.state _
      (CompletePassive.emit _ CompleteProduct.account_safe (.queued receipt) rfl (fun _ => rfl))

theorem Child.checked (token : Child) : Checked token.action := by
  cases token with
  | release peer =>
    exact CompletePoll.state _
      (CompleteSource.original peer CompleteProduct.Safe CompleteProduct.account_safe)
  | flushedSend pid =>
    exact CompletePoll.state _
      (CompleteSend.flushed CompleteProduct.Safe CompleteProduct.account_safe pid)

theorem Shape.checked (shape : Shape action) : Checked action := by
  induction shape with
  | pure value => exact CompletePoll.pure_checked _ CompleteProduct.account_safe value
  | native token => exact token.checked
  | leaf source => exact source.checked
  | child token => exact token.checked
  | failed failure next =>
    intro w h before
    obtain ⟨reason,run⟩ := failure.run w h
    exact ⟨[],by simp only [runPrefix_bind,run,List.append_nil],by simpa only [runPrefix_bind,run] using Consume.Leaf.carrier_safe h w before,by simp only [runPrefix_bind,run]⟩
  | bind head tail ihHead ihTail => exact CompletePoll.bind_checked _ ihHead ihTail
  | marked label shape ih => exact ih

theorem Shape.normal (shape : Shape action) (before : Carrier h w)
    (performed : runPrefix action w h = (.ok (value,u),middle)) : Carrier middle u := by
  obtain ⟨suffix,extended,safe,kept⟩ := shape.checked w h before
  rw [performed] at kept
  exact kept

abbrev leafPoints := Consume.Leaf.armPoints Wheel.Points.children

noncomputable def leafContracts : Consume.Leaf.ChildContracts leafPoints leafPoints Carrier :=
  Consume.Leaf.arm_children (fun _ _ h => h) (Wheel.Points.wheel_contract (fun _ _ h => h))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
