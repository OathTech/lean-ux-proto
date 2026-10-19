import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteEncryptSource

/-! Consuming the device encryption ring changes scheduling state without
consuming per-peer owning batches. Both actual ring receipts are passive for
births and terminal demands, independently of native endpoint erasure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations StagedTerminalComplete CompleteCarrier
set_option maxHeartbeats 600000

noncomputable def demand? (event : Event) : Option Unit := by
  classical
  exact if birthPackets event = [] ∧ Quiet event then none else some ()

theorem demand_none (birth : birthPackets event = []) (terminal : Quiet event) :
    demand? event = none := by simp only [demand?,birth,terminal,and_self,ite_true]

theorem focused (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
    (encode : E → Event) (decode : Event → Option E) (body : PrefixM E α)
    (appends : Appends body) (quiet : HistoryFrame (demand? ∘ encode) body)
    (native : Leanux.M α) (erases : ErasesPrefix body native)
    (frame : ∀ h ledger, Preserves (fun w : World => Inv h ledger debts locals w.wg) native) :
    CompletePoll.Checked debts locals Safe (focusPrefix encode decode body) := by
  intro w h before
  obtain ⟨ledger,accounted⟩ := before
  obtain ⟨suffix,extended⟩ := appends w (h.filterMap decode)
  have filtered := quiet w (h.filterMap decode)
  rw [extended,List.filterMap_append] at filtered
  have empty : suffix.filterMap (demand? ∘ encode) = [] := List.append_right_eq_self.mp filtered
  have harmless : ∀ event ∈ suffix, birthPackets (encode event) = [] ∧ Quiet (encode event) := by
    intro event member
    have absent := List.filterMap_eq_nil_iff.mp empty event member
    classical
    by_cases good : birthPackets (encode event) = [] ∧ Quiet (encode event)
    · exact good
    · simp only [Function.comp_apply,demand?,good,ite_false] at absent
      cases absent
  have grow : ∀ v, Accounted h ledger debts locals v → Accounted (h ++ suffix.map encode) ledger debts locals v := by
    intro v before
    apply before.append_quiet
    · intro event member
      obtain ⟨e,mem,rfl⟩ := List.mem_map.mp member
      exact (harmless e mem).1
    · intro event member
      obtain ⟨e,mem,rfl⟩ := List.mem_map.mp member
      exact (harmless e mem).2
  rw [focusPrefix_suffix encode decode body w h _ suffix (Prod.ext rfl extended)]
  refine ⟨suffix.map encode,rfl,accountSafe _ _ _ (grow w.wg accounted),?_⟩
  cases result : (runPrefix body w (h.filterMap decode)).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨value,v⟩ := out
    have run := (erases w (h.filterMap decode)).symm.trans result
    exact ⟨ledger,grow v.wg ⟨(hoare_iff_run _ _ _).mp (frame h ledger) w value v accounted.entry run,accounted.complete⟩⟩

theorem poll_frame : SameView StagedEntry.view TxRing.pollSource := by
  unfold TxRing.pollSource
  apply SameView.bind (TimerFrames.store getDev_sameWGStore)
  intro d
  exact (ReceiveFrames.device (fun x => {x with encryptQueue := d.encryptQueue.consume.2})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).bind
    (fun _ => SameView.pure _ _)

/-- Actual ring consumption retains the same paired ledger, including Stop. -/
theorem checked (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h) :
    CompletePoll.Checked debts locals Safe hooks.poll := by
  apply focused Safe accountSafe Event.old old? Journal.poll
  · exact Appends.receiptObserved (Appends.focus _ _ _)
  · exact HistoryFrame.receiptObserved
      (focusPrefix_other Journal.Event.ring Journal.ring? (demand? ∘ Event.old)
        (fun _ => demand_none rfl (fun _ => rfl)) _)
      (fun _ => demand_none rfl (fun _ => rfl))
  · intro w h
    have projected := congrArg Prod.fst (Journal.poll_projects w h)
    have maps : (fun x : Option (List SkbId) × World => (id x.1,x.2)) = id := by funext ⟨value,v⟩; rfl
    rw [maps,Except.map_id] at projected
    exact projected.symm
  · intro h ledger
    apply PublicationPoll.native_product (Inv h ledger debts locals)
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a value v b before run
    exact before.same_view ((ProjectedAction.iff_run_ambient _ _ _).mp poll_frame w a value v b run)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRing
