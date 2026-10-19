import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixAdmissionCheckpoint
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteFrontChecked

/-! Every journal prefix of the actual routed front is certified, including
the disposal checkpoint preceding its routed receipt. The same source
checkpoint supplies its full ledger and the successor's routed birth. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Admission
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal CompleteCarrier
open StagedAdmission.Front

theorem input_accounted (input : Input) (before : Accounted h ledger debts locals w) :
    Accounted (h ++ [.transmitInput input]) ledger debts locals w :=
  before.append_quiet [.transmitInput input]
    (fun _ member => by cases List.mem_singleton.mp member; rfl)
    (fun _ member => by cases List.mem_singleton.mp member; intro position; rfl)

theorem front_normal_cuts (input : Input) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
    (before : Accounted h ledger debts locals w)
    (a b : Ambient) (v : WGWorld) (history : List Event) (value : Except Int PeerId)
    (run : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu)
      w a h = (.ok ((value,v),b),history)) :
    ∃ suffix after, history = h ++ suffix ∧ Cuts Safe h suffix ∧
      Accounted history after debts locals v := by
  let entry := coreEntry before.entry.core
  obtain ⟨prior,r,after,position,_,_,atAfter,_,normal⟩ :=
    normal_result entry input rfl a b v history value run
  obtain ⟨priorLedger,snapshot,cut,_⟩ := normal.2.2.2.2
  have initial : Accounted (entry.withInput input).history (entry.withInput input).ledger
      debts locals (entry.withInput input).world := input_accounted input before
  have material := Material.front_checked input w a h
  have ownership := Ownership.front_checked input w a h
  rw [run,position] at material ownership
  have priorAccount := checkpoint_accounted cut (entry.withInput_canonical input rfl) initial
    (material_checkpoint cut material.1) (ownership_checkpoint cut ownership.1)
  have finalAccount : Accounted (prior ++ [routedEvent input r]) after debts locals v := by
    rw [←atAfter]
    exact normal_accounted normal initial (by rw [atAfter]; exact material.2)
      (by rw [atAfter]; exact ownership.2)
  obtain ⟨middle,priorHistory,middleCuts⟩ := checkpoint_cuts cut
    (accountSafe _ _ _ initial) (accountSafe _ _ _ priorAccount)
  have first := (Cuts.singleton (accountSafe _ _ _ before) (accountSafe _ _ _ initial)).append middleCuts
  have last := Cuts.singleton (accountSafe _ _ _ priorAccount) (accountSafe _ _ _ finalAccount)
  rw [priorHistory] at last
  have last' : Cuts Safe (h ++ ([.transmitInput input] ++ middle)) [routedEvent input r] := by
    simpa only [Entry.withInput,coreEntry,entry,List.append_assoc] using last
  refine ⟨([.transmitInput input] ++ middle) ++ [routedEvent input r],after,?_,?_,?_⟩
  · rw [position,priorHistory]
    simp only [Entry.withInput,coreEntry,entry,List.append_assoc]
  · exact first.append last'
  · rw [position]
    exact finalAccount

theorem front_stopped_cuts (input : Input) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
    (before : Accounted h ledger debts locals w)
    (a : Ambient) (history : List Event) (stop : Stop)
    (run : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu)
      w a h = (.error stop,history)) :
    ∃ suffix, history = h ++ suffix ∧ Cuts Safe h suffix := by
  obtain ⟨after,snapshot,cut,accounted,_,_⟩ := CompleteFront.front_stopped input before a history stop run
  have initial := input_accounted input before
  obtain ⟨middle,equal,cuts⟩ := checkpoint_cuts cut
    (accountSafe _ _ _ initial) (accountSafe after history snapshot accounted)
  refine ⟨[.transmitInput input] ++ middle,?_,?_⟩
  · simpa only [Entry.withInput,coreEntry,List.append_assoc] using equal
  · exact (Cuts.singleton (accountSafe _ _ _ before) (accountSafe _ _ _ initial)).append cuts

theorem front_cuts (input : Input) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
    (w : WGWorld) (a : Ambient) (h : List Event) (before : Carrier debts locals h w a) :
    ∃ suffix, (runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu) w a h).2 =
      h ++ suffix ∧ Cuts Safe h suffix := by
  obtain ⟨ledger,accounted⟩ := before
  cases performed : runWGPrefix (CausalJournal.front input.family input.address input.packets input.mtu) w a h with
  | mk outcome last =>
    cases outcome with
    | error stop => exact front_stopped_cuts input Safe accountSafe accounted a last stop performed
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      obtain ⟨suffix,_,extended,cuts,_⟩ := front_normal_cuts input Safe accountSafe accounted a b v last value performed
      exact ⟨suffix,extended,cuts⟩

theorem front (input : Input) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h) :
    StateEnsures (Carrier debts locals) Safe
      (CausalJournal.front input.family input.address input.packets input.mtu)
      (fun _ => Carrier debts locals) :=
  StateEnsures.of_cuts (CompleteFront.checked input Safe accountSafe)
    (front_cuts input Safe accountSafe)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Admission
