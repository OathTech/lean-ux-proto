import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionInteriorPublicationSource

/-! Native frames at the fixed encryption-publication sites. The head write
uses material/ownership preservation, not equality of the whole packet store.
The history is unchanged until the separate original release callback. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CompleteCarrier

theorem check_view (pid : PeerId) (first : SkbId) : SameView StagedEntry.view (queueCheck pid first) := by
  intro initial
  unfold queueCheck
  apply hoare_bind _ _ (Queued.read pid initial)
  intro peer
  split
  · exact hoare_liftAmbient (AmbientM.invariant _) _
  · exact preserves_pure _

theorem work_append_view (pid : PeerId) :
    SameView StagedEntry.view (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b performed
  cases value
  simp only [modifyDev] at performed
  cases performed
  change StagedEntry.view {dev := w.dev.map (fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]})} =
    StagedEntry.view {dev := w.dev}
  cases w.dev <;> rfl

theorem cpu_view (pid : PeerId) : SameView StagedEntry.view (cpumaskChooseOnline pid) := by
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold cpumaskChooseOnline
  simp only [Nat.mod_one,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (allocation_release_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | (allocation_release_head ForIn.forIn
       apply list_view_spec id (fun w => StagedEntry.view w = initial)
       intro x b
       change Preserves (fun w => StagedEntry.view w = initial) _)
    | queued_entry_step initial

theorem schedule_view (pid : PeerId) : SameView StagedEntry.view (scheduleNative pid) := by
  have readDev : SameView StagedEntry.view getDev :=
    getDev_sameWGStore.of_factor (fun store => StagedEntry.view {dev := store.dev}) StagedEntry.view (fun _ => rfl)
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  unfold scheduleNative
  simp only [peekQueuedUnit,recordQueued]
  repeat' first
    | (allocation_release_head cpumaskChooseOnline; exact cpu_view pid initial)
    | (allocation_release_head getDev; exact readDev initial)
    | (allocation_release_head modifyDev; exact work_append_view pid initial)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | allocation_release_step

theorem mark_keeps (first : SkbId) (state : PacketState) :
    Preserves (Inv history ledger debts locals) (setTxSkb first fun p => {p with state}) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before performed
  cases value
  exact publication_mark_native first state before a b performed

private theorem native_keeps (action : WG.M α)
    (keeps : ∀ h, Preserves (Inv h ledger debts locals) action) :
    PrefixPreserves (fun h w => Accounted h ledger debts locals w.wg) (fun _ => True)
      (liftPrefix (liftWG action)) := by
  intro w h before
  refine ⟨[],by simp [runPrefix_lift],trivial,?_⟩
  rw [runPrefix_lift]
  cases performed : (liftWG action).run w with
  | error stop => trivial
  | ok out =>
    obtain ⟨value,v⟩ := out
    exact ⟨(hoare_iff_run _ _ _).mp (PublicationPoll.native_product _ _ (keeps h))
      w value v before.entry performed,before.complete⟩

theorem publication_prefix_accounted (site : PublicationSite)
    (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix (publicationPrefixAt site items state) w history = (.ok (pair,v),after)) :
    Accounted after ledger debts locals v.wg := by
  have kept : PrefixPreserves (fun h w => Accounted h ledger debts locals w.wg) (fun _ => True)
      (publicationPrefixAt site items state) := by
    unfold publicationPrefixAt
    apply PrefixPreserves.bind (native_keeps _ (fun _ => StagedEntry.native (publication_borrow_view items)))
    intro pair
    obtain ⟨first,pid⟩ := pair
    cases site <;>
      repeat' first
        | (nonce_product_head check; exact native_keeps _ (fun _ => StagedEntry.native (check_view pid first)))
        | (nonce_product_head mark; exact native_keeps _ (fun _ => mark_keeps first state))
        | (nonce_product_head schedule; exact native_keeps _ (fun _ => StagedEntry.native (schedule_view pid)))
        | (nonce_product_head Bind.bind; apply PrefixPreserves.bind)
        | (nonce_product_head Pure.pure; exact PrefixPreserves.pure (fun _ _ _ => trivial) _)
        | maintenance_intro
        | dsimp (config := {failIfUnchanged := true}) only
  obtain ⟨_,_,_,normal⟩ := kept w history before
  simpa only [performed] using normal

theorem publication_prefix_history (site : PublicationSite) (items : List SkbId) (state : PacketState) :
    HistoryFrame (fun e : CausalJournal.Event => some e) (publicationPrefixAt site items state) := by
  unfold publicationPrefixAt borrow check mark schedule
  repeat' first
    | exact HistoryFrame.lift _ _
    | exact HistoryFrame.pure _ _
    | apply HistoryFrame.bind
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | cases site

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionInterior
