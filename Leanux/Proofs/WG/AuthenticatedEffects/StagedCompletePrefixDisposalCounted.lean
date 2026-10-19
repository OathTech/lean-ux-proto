import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDisposalHistory

/-! Counted purge and original peer release expose their zero-or-one receipt
shape. Existing exact settlements certify the nonquiet event, including a
release whose native timer/retirement finish subsequently stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Disposal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations CompleteCarrier
open HandshakeSecurity.StagedDisposal (releaseCut)

theorem purge_cuts (pid : PeerId) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
    (w : WGWorld) (a : Ambient) (h : List Event) (before : Carrier debts locals h w a) :
    ∃ suffix, (runWGPrefix (CausalJournal.stagedPurge pid) w a h).2 = h ++ suffix ∧ Cuts Safe h suffix := by
  obtain ⟨ledger,accounted⟩ := before
  obtain ⟨_,_,finished,_⟩ := CompleteSource.purge pid Safe accountSafe w a h ⟨ledger,accounted⟩
  change Safe (runWGPrefix (CausalJournal.stagedPurge pid) w a h).2 at finished
  rw [Purge.run] at finished ⊢
  cases native : ((purgeStagedPackets pid).run w).run a with
  | error stop => exact ⟨[],by simp,Cuts.nil (accountSafe _ _ _ accounted)⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    cases value
    rw [native] at finished
    exact ⟨[_],rfl,Cuts.singleton (accountSafe _ _ _ accounted) finished⟩

theorem purge (pid : PeerId) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h) :
    StateEnsures (Carrier debts locals) Safe (CausalJournal.stagedPurge pid)
      (fun _ => Carrier debts locals) :=
  StateEnsures.of_cuts (CompleteSource.purge pid Safe accountSafe) (purge_cuts pid Safe accountSafe)

theorem original_cuts (peer : Option PeerId) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
    (w : WGWorld) (a : Ambient) (h : List Event) (before : Carrier debts locals h w a) :
    ∃ suffix, (runWGPrefix (CausalJournal.peerRelease peer) w a h).2 = h ++ suffix ∧ Cuts Safe h suffix := by
  obtain ⟨ledger,accounted⟩ := before
  obtain ⟨_,_,finished,_⟩ := CompleteSource.original peer Safe accountSafe w a h ⟨ledger,accounted⟩
  change Safe (runWGPrefix (CausalJournal.peerRelease peer) w a h).2 at finished
  have equation := StagedAdmission.Front.put_run peer w a h
  change runWGPrefix (CausalJournal.peerRelease peer) w a h = _ at equation
  rw [equation] at finished ⊢
  cases native : ((releaseCut peer).run w).run a with
  | error stop => exact ⟨[],by simp,Cuts.nil (accountSafe _ _ _ accounted)⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    rw [native] at finished
    cases value with
    | none => exact ⟨[_],rfl,Cuts.singleton (accountSafe _ _ _ accounted) finished⟩
    | some pair => exact ⟨[_],rfl,Cuts.singleton (accountSafe _ _ _ accounted) finished⟩

theorem original (peer : Option PeerId) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h) :
    StateEnsures (Carrier debts locals) Safe (CausalJournal.peerRelease peer)
      (fun _ => Carrier debts locals) :=
  StateEnsures.of_cuts (CompleteSource.original peer Safe accountSafe) (original_cuts peer Safe accountSafe)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Disposal
