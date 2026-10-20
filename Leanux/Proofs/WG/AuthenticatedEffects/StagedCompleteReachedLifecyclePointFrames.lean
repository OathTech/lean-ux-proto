import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointSource

/-! Actual native frames. The weaker Account at setup/newlink is deliberate;
allocation state is re-established only at the completed creation boundary. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity
open TransmitSecurity.Staged.Obligations

abbrev WGFrame (body : WG.M α) := SameView StagedEntry.view body

theorem wg_frame (body : WG.M α) (frame : WGFrame body) :
    SameView (fun w : World => StagedEntry.view w.wg) (liftWG body) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w value v run
  change (body.run w.wg).run w.ambient >>= _ = _ at run
  cases performed : (body.run w.wg).run w.ambient with
  | error reason => simp [performed] at run
  | ok out =>
    obtain ⟨⟨result,u⟩,a⟩ := out
    simp only [performed] at run
    cases run
    exact (ProjectedAction.iff_run_ambient _ _ _).mp frame _ _ _ _ _ performed

def Native.Entry : {α : Type} → {body : PrefixM Event α} → Native body → History → World → Prop
  | _,_,.quiet ..,h,w => Account h w
  | _,_,.metadata ..,h,w => Account h w
  | _,_,.routing ..,h,w => Account h w
  | _,_,.setup,h,w => ∃ledger,CompleteCarrier.Accounted h ledger [] [] w.wg ∧ w.wg.dev=none
  | _,_,.newlink,h,w => ∃ledger start,Creating h ledger start w.wg
  | _,_,.erase,h,w => ∃ledger,CompleteCarrier.Accounted h ledger [] [] w.wg ∧ Retired.NoPending ledger
  | _,_,.check,h,w => ∃ledger holders,CompleteRetired.GuardEntry h ledger holders w.wg

theorem Native.entry_account (token : Native body) (before : token.Entry h w) : Account h w := by
  cases token with
  | quiet => exact before
  | metadata => exact before
  | routing => exact before
  | setup => exact ⟨before.choose,before.choose_spec.1⟩
  | newlink => obtain ⟨ledger,start,creating⟩ := before; exact ⟨ledger,creating.account⟩
  | erase => exact ⟨before.choose,before.choose_spec.1⟩
  | check => obtain ⟨ledger,holders,entry⟩ := before; exact ⟨ledger,entry.accounted⟩

private theorem lift_normal (body : WG.M α)
    (post : ∀ value v a, (body.run w.wg).run w.ambient=.ok ((value,v),a) →
      ∃ledger,CompleteCarrier.Accounted h ledger [] [] v)
    (performed : runPrefix (liftPrefix (liftWG body)) w h=(.ok (value,u),last)) : Account last u := by
  rw [runPrefix_lift] at performed
  have history : last=h := (congrArg Prod.snd performed).symm
  subst last
  have run := congrArg Prod.fst performed
  change ((body.run w.wg).run w.ambient >>= _) = .ok (value,u) at run
  cases native : (body.run w.wg).run w.ambient with
  | error reason => simp [native] at run
  | ok out =>
    obtain ⟨⟨result,v⟩,a⟩ := out
    simp only [native] at run
    cases run
    exact post result v a native

theorem Native.normal (token : Native body) (before : token.Entry h w)
    (performed : runPrefix body w h=(.ok (value,u),last)) : Account last u := by
  cases token with
  | quiet action frame =>
    rw [runPrefix_lift] at performed
    have history : last=h := (congrArg Prod.snd performed).symm
    subst last
    obtain ⟨ledger,account⟩ := before
    exact ⟨ledger,account.same_view ((ProjectedAction.iff_run _ _ _).mp frame _ _ _
      (congrArg Prod.fst performed))⟩
  | metadata action source =>
    obtain ⟨ledger,account⟩ := before
    exact lift_normal action (fun _ _ _ run=>⟨ledger,account.same_view
      ((ProjectedAction.iff_run_ambient _ _ _).mp source.frame _ _ _ _ _ run)⟩) performed
  | routing action source =>
    obtain ⟨ledger,account⟩ := before
    exact lift_normal action (fun _ _ _ run=>⟨ledger,account.same_view
      ((ProjectedAction.iff_run_ambient _ _ _).mp source.frame _ _ _ _ _ run)⟩) performed
  | setup =>
    obtain ⟨ledger,account,absent⟩ := before
    apply lift_normal _ (fun result v a run=>?_) performed
    rw [setup_run] at run
    cases run
    exact ⟨ledger,setup_accounted account absent⟩
  | newlink =>
    obtain ⟨ledger,start,creating⟩ := before
    exact lift_normal _ (fun _ _ _ run=>⟨ledger,(creating.newlink run).1⟩) performed
  | erase =>
    obtain ⟨ledger,account,settled⟩ := before
    exact lift_normal _ (fun _ _ _ run=>⟨ledger,erase_accounted account settled run⟩) performed
  | check =>
    obtain ⟨ledger,holders,entry⟩ := before
    apply lift_normal _ (fun result v a run=>?_) performed
    cases result
    rw [(guard_no_pending entry run).1]
    exact ⟨ledger,entry.accounted⟩

def Family.Entry (family : Family) (h : History) (w : World) : Prop := match family with
  | .staging _ | .keepalive _ => CompleteProduct.Carrier h w
  | _ => Account h w

def Child.Entry : {α : Type} → {body : PrefixM Event α} → Child body → History → World → Prop
  | _,_,.family source => source.Entry

theorem Child.entry_account (token : Child body) (before : token.Entry h w) : Account h w := by
  cases token with
  | family family => cases family <;> first | exact before | exact account_of_carrier before

theorem Child.normal (token : Child body) (before : token.Entry h w)
    (performed : runPrefix body w h=(.ok (value,u),last)) : Account last u := by
  have full {α} {body : PrefixM Event α} (checked : CompleteProduct.Checked body) {value : α}
      (before : CompleteProduct.Carrier h w)
      (run : runPrefix body w h=(.ok (value,u),last)) : Account last u := by
    obtain ⟨_,_,_,post⟩ := checked w h before
    rw [run] at post
    exact post.1
  have state {α} {body : WGPrefix Event α}
      (checked : CompletePassive.Checked [] [] CompleteProduct.Safe body) {value : α}
      (before : Account h w)
      (run : runPrefix (liftWGObserver body) w h=(.ok (value,u),last)) : Account last u := by
    obtain ⟨_,_,_,post⟩ := checked.liftWGObserver w h before
    rw [run] at post
    exact post
  cases token with
  | family family =>
    cases family with
    | staging pid => exact full (CompleteProduct.state (CompleteProduct.fixture _ _ (CompleteProduct.staging pid))) before performed
    | keepalive pid => exact full (CompleteProduct.state (CompleteProduct.fixture _ _ (CompleteProduct.keepalive pid))) before performed
    | drain upTo => exact state (CompleteSendDrain.checked CompleteProduct.Safe CompleteProduct.account_safe upTo) before performed
    | purge pid => exact state (CompleteSource.purge pid CompleteProduct.Safe CompleteProduct.account_safe) before performed
    | release peer => exact state (CompleteSource.original peer CompleteProduct.Safe CompleteProduct.account_safe) before performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
