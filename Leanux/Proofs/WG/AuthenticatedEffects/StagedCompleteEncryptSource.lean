import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteEncryptPublication
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryEncryptFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePollBase

/-! The whole encryption callback retains forward and converse ticket
accounting on one ledger. Its actual publication has a source-funded nonfinal
repayment; ordinary encryption receipts carry no terminal demand. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteEncrypt
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations StagedTerminalComplete HandshakeSecurity.StagedDisposal
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem focused_history (encode : E → CausalJournal.Event) (decode : CausalJournal.Event → Option E)
    (quiet : ∀ e, Quiet (encode e)) (body : PrefixM E α) :
    Driver.ProductHistorySafe (fun h => Complete h ledger) (focusPrefix encode decode body) := by
  intro w h before
  obtain ⟨suffix,extended⟩ := Appends.focus encode decode body w h
  have kept : Complete (runPrefix (focusPrefix encode decode body) w h).2 ledger := by
    change Complete (h ++ _) ledger
    apply before.append_quiet
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact quiet original
  refine ⟨suffix,extended,kept,?_⟩
  cases (runPrefix (focusPrefix encode decode body) w h).1 <;> trivial

theorem after_history (item : List SkbId) (skb : SkbId) (head : RunWitness DataPacket) :
    Driver.ProductHistorySafe (fun h => Complete h ledger)
      (EncryptionSource.afterHead
        (EncryptionSource.observed (Event.old ∘ Journal.Event.encrypted)
          (fun event => (old? event).bind Journal.encryption?) Event.stagedDisposal stagedDisposal?)
        item skb head) := by
  unfold EncryptionSource.afterHead
  simp only [EncryptionSource.observed,EncryptionSource.focused]
  repeat' first
    | (driver_history_head Publication.observed;
        exact Driver.History.product_state (publication_history _ _))
    | (driver_history_head focusPrefix; exact focused_history _ _ (fun _ _ => rfl) _)
    | driver_product_history_step

theorem history (item : Option (List SkbId)) :
    Driver.ProductHistorySafe (fun h => Complete h ledger) (CausalJournal.encrypt item) := by
  unfold CausalJournal.encrypt
  apply CallbackHistory.product_receipt _ _ _
    (fun r => by
      intro w h before
      have kept := before.append_quiet (suffix := [.old (.encryptionReturn item r)])
        (by intro event member position; cases List.mem_singleton.mp member; rfl)
      exact ⟨[_],rfl,kept,kept⟩)
  unfold EncryptionSource.tail
  simp only [EncryptionSource.observed,EncryptionSource.focused]
  repeat' first
    | (driver_history_head EncryptionSource.afterHead; exact after_history _ _ _)
    | (driver_history_head focusPrefix; exact focused_history _ _ (fun _ _ => rfl) _)
    | driver_product_history_step

theorem erases (items : Option (List SkbId)) :
    ErasesPrefix (CausalJournal.encrypt items) (RxWorkers.encryptStepTailSource items) := by
  apply CallbackFrames.product_erases old? (CausalJournal.encrypt_projects items)
  intro w h
  have projected := congrArg Prod.fst (Journal.encrypt_projects items w h)
  have maps : (fun x : Bool × World => (id x.1,x.2)) = id := by funext ⟨value,v⟩; rfl
  rw [maps,Except.map_id] at projected
  exact projected.symm

theorem birth_suffix (items : Option (List SkbId)) (w : World) (h : List CausalJournal.Event) :
    ∃ suffix, (runPrefix (CausalJournal.encrypt items) w h).2 = h ++ suffix ∧
      ∀ event ∈ suffix, birthPackets event = [] := by
  classical
  let ρ : CausalJournal.Event → Option Unit := fun event => if birthPackets event = [] then none else some ()
  have quiet := CallbackQuiet.encrypt ρ (fun _ => by simp [ρ,birthPackets])
    (fun _ => by simp [ρ,birthPackets]) (fun _ _ => by simp [ρ,birthPackets]) items
  obtain ⟨suffix,extended⟩ := quiet.1 w h
  refine ⟨suffix,extended,?_⟩
  have filtered := quiet.2 w h
  rw [extended,List.filterMap_append] at filtered
  have empty : suffix.filterMap ρ = [] := List.append_right_eq_self.mp filtered
  intro event member
  by_cases noBirth : birthPackets event = []
  · exact noBirth
  have bad : () ∈ suffix.filterMap ρ := List.mem_filterMap.mpr ⟨event,member,by simp [ρ,noBirth]⟩
  rw [empty] at bad
  cases bad

/-- The actual encryption callback preserves same-ledger paired accounting
on normal return and retains an accounted historical cut on Stop. -/
theorem checked (Safe : List CausalJournal.Event → Prop)
    (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w → Safe h)
    (item : Option (List SkbId)) : CompletePoll.Checked debts locals Safe (CausalJournal.encrypt item) := by
  intro w h before
  obtain ⟨ledger,accounted⟩ := before
  obtain ⟨suffix,extended,birthFree⟩ := birth_suffix item w h
  obtain ⟨_,_,complete,_⟩ := history item w h accounted.complete
  refine ⟨suffix,extended,?_,?_⟩
  · apply accountSafe ledger _ w.wg
    refine ⟨?_,complete⟩
    rw [extended]
    exact Queued.Inv.history accounted.entry suffix birthFree
  · cases result : (runPrefix (CausalJournal.encrypt item) w h).1 with
    | error stop => trivial
    | ok out =>
      obtain ⟨value,v⟩ := out
      have native := (erases item w h).symm.trans result
      have kept := (hoare_iff_run _ _ _).mp (Encrypt.tail item) w value v accounted.entry native
      refine ⟨ledger,?_,complete⟩
      rw [extended]
      exact Queued.Inv.history kept suffix birthFree

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteEncrypt
