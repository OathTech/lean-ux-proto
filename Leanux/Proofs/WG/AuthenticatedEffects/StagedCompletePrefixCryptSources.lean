import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixCryptQuiet
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDecryptSource

/-! Actual encryption-ring polling, decryption preparation and encryption
retain every logical prefix. Encryption uses a source-proved unchanged ledger,
its birth-free suffix and complete receipt scan, not a final-ledger rollback. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Crypt
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations StagedTerminalComplete CompleteCarrier
open CompleteRing (demand? demand_none)

theorem poll (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h) :
    Checked debts locals Safe hooks.poll := by
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
    exact before.same_view ((ProjectedAction.iff_run_ambient _ _ _).mp CompleteRing.poll_frame w a value v b run)


theorem prepare (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h) :
    Checked debts locals Safe hooks.prepare := by
  apply focused Safe accountSafe Event.old old?
    (TransportDriver.prepare Journal.Event.rxOrigin Journal.origin?)
  · exact Appends.focus _ _ _
  · exact focusPrefix_other Journal.Event.rxOrigin Journal.origin? (CompleteRing.demand? ∘ Event.old)
      (fun _ => CompleteRing.demand_none rfl (fun _ => rfl)) _
  · exact TransportDriver.prepare_erases _ _
  · intro h ledger
    apply PublicationPoll.native_product (Inv h ledger debts locals)
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a value v b before run
    exact before.same_view ((ProjectedAction.iff_run_ambient _ _ _).mp CompleteDecrypt.prepare w a value v b run)


theorem encrypt_cuts (Safe : List Event→Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w→Safe h)
    (item : Option (List SkbId)) (w : World) (h : List Event)
    (before : CompletePoll.Carrier debts locals h w) :
    ∃ suffix, (runPrefix (CausalJournal.encrypt item) w h).2=h++suffix ∧ Cuts Safe h suffix := by
  obtain ⟨ledger,accounted⟩ := before
  obtain ⟨suffix,extended,births⟩ := CompleteEncrypt.birth_suffix item w h
  obtain ⟨_,_,complete,_⟩ := CompleteEncrypt.history item w h accounted.complete
  refine ⟨suffix,extended,FixedHistory.cuts Safe accountSafe accounted births ?_⟩
  rwa [extended] at complete

theorem encrypt (Safe : List Event→Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w→Safe h)
    (item : Option (List SkbId)) : Checked debts locals Safe (CausalJournal.encrypt item) :=
  Ensures.of_cuts (CompleteEncrypt.checked Safe accountSafe item) (encrypt_cuts Safe accountSafe item)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Crypt
