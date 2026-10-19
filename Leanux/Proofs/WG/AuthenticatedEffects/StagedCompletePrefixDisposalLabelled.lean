import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDisposalCounted
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDisposalNested
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCreateFree

/-! A source-labelled free crosses quiet access prefixes and then exactly
one terminal receipt. Its first settlement requires the actual pending
ticket; ordinary later cleanup does not create another terminal outcome. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Disposal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations CompleteCarrier HandshakeSecurity.StagedConservation

theorem cleanup_cuts (skb : SkbId) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
    (before : Accounted h ledger debts locals w.wg) :
    ∃ suffix, (runPrefix (FirstTerminal.cleanupFree skb) w h).2 = h ++ suffix ∧ Cuts Safe h suffix :=
  focused_cuts (TxDisposition.nativeAccess (freeTxSkbPrefix skb)) Safe accountSafe before

theorem labelled_cuts (reason : Terminal.Reason) (skb : SkbId) (phase : TxLocalPhase)
    (Safe : List Event → Prop)
    (accountSafe : ∀ ledger locals h w, Accounted h ledger debts locals w → Safe h)
    (performed : runPrefix (FirstTerminal.cleanupFree skb) w h = (.ok ((),v),h ++ access))
    (before : Accounted h ledger debts (⟨phase,pid,skb :: remaining⟩ :: locals) w.wg)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin h position ordinal generation skb material) :
    let receipt : Terminal.Receipt := ⟨reason,skb,⟨(),w,v⟩⟩
    let outcome := Staged.Obligations.Terminal.disposed (h ++ access).length reason
    let after := settle [ticket] outcome ledger
    let journal := (h ++ access) ++ [Event.terminalDrop receipt]
    runPrefix (CreateDisposal.free reason skb) w h = (.ok ((),v),journal) ∧
      Cuts Safe h (access ++ [Event.terminalDrop receipt]) ∧
      Staged.Obligations.Step ledger after ∧
      Accounted journal after debts (⟨phase,pid,remaining⟩ :: locals) v.wg ∧
      (ticket,Status.terminal outcome) ∈ after := by
  dsimp only
  obtain ⟨observed,step,accounted,terminal⟩ :=
    CompleteCreate.labelled_free reason skb phase performed before pending origin
  obtain ⟨suffix,extended,cuts⟩ := cleanup_cuts skb Safe (fun ledger h w => accountSafe ledger _ h w) before
  rw [performed] at extended
  have same : access = suffix := List.append_cancel_left extended
  subst suffix
  exact ⟨observed,cuts.append (Cuts.singleton cuts.last (accountSafe _ _ _ _ accounted)),
    step,accounted,terminal⟩

/-- Backing of the same pending ticket makes the native free total. No
completed-free premise or invented reason is supplied by an enclosing run. -/
theorem labelled_total (reason : Terminal.Reason) (skb : SkbId) (phase : TxLocalPhase)
    (Safe : List Event → Prop)
    (accountSafe : ∀ ledger locals h w, Accounted h ledger debts locals w → Safe h)
    (before : Accounted h ledger debts (⟨phase,pid,skb :: remaining⟩ :: locals) w.wg)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin h position ordinal generation skb material) :
    ∃ v access,
      runPrefix (FirstTerminal.cleanupFree skb) w h = (.ok ((),v),h ++ access) ∧
      let receipt : Terminal.Receipt := ⟨reason,skb,⟨(),w,v⟩⟩
      let outcome := Staged.Obligations.Terminal.disposed (h ++ access).length reason
      let after := settle [ticket] outcome ledger
      let journal := (h ++ access) ++ [Event.terminalDrop receipt]
      runPrefix (CreateDisposal.free reason skb) w h = (.ok ((),v),journal) ∧
        Cuts Safe h (access ++ [Event.terminalDrop receipt]) ∧
        Staged.Obligations.Step ledger after ∧
        Accounted journal after debts (⟨phase,pid,remaining⟩ :: locals) v.wg ∧
        (ticket,Status.terminal outcome) ∈ after := by
  have backed := (before.entry.core.physical.resident ticket position ordinal pending).at_origin origin
  obtain ⟨v,access,performed⟩ := CreateDisposal.cleanup_total backed.2 h
  exact ⟨v,access,performed,labelled_cuts reason skb phase Safe accountSafe performed before pending origin⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Disposal
