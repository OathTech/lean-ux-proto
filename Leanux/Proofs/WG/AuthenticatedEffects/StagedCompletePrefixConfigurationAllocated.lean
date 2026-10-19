import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixPassive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocatedCarrier

/-! Allocation freshness is transported beside a separately established
prefix contract for the same source. Native erasure supplies only this
normal-state companion, never the journal-prefix certificate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ConfigurationAllocated
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal StackOwnership
open CompleteAllocated (Carrier)
abbrev Checked (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (Safe : List Event→Prop) (body : WGPrefix Event α) : Prop :=
  StateEnsures (Carrier debts locals) Safe body (fun _=>Carrier debts locals)
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event→Prop)
variable (accountSafe : ∀ ledger h w, CompleteCarrier.Accounted h ledger debts locals w→Safe h)

theorem pair {action : WGPrefix Event α} {native : WG.M α}
    (prefixes : Passive.Checked debts locals Safe action)
    (erases : ErasesStatePrefix action native) (allocated : Preserves Allocated native) :
    Checked debts locals Safe action := by
  intro w a h before
  obtain ⟨suffix,extended,all,kept⟩ := prefixes w a h ⟨before.1.1,before.2⟩
  refine ⟨suffix,extended,all,?_⟩
  cases performed : (runPrefix (action.run w) a h).1 with
  | error reason=>trivial
  | ok out=>
    obtain ⟨⟨value,v⟩,b⟩ := out
    rw [performed] at kept
    exact ⟨⟨kept.1,(hoare_iff_run_ambient _ _ _).mp allocated w a value v b before.1.2
      ((erases w a h).symm.trans performed)⟩,kept.2⟩

theorem pure_checked (value : α) : Checked debts locals Safe (pure value) :=
  StateEnsures.pure value (fun _ _ _ before=>before)

theorem list {α β : Type} (xs : List α) (initial : β) (body : α→β→WGPrefix Event (ForInStep β))
    (checked : ∀ item acc, StateEnsures (Carrier debts locals) Safe (body item acc)
      (fun _=>Carrier debts locals)) :
    Checked debts locals Safe (forIn xs initial body) :=
  StateEnsures.forIn xs initial body (fun _=>Carrier debts locals) checked

include accountSafe in
theorem passive (action : WG.M α) (entry : SameView StagedEntry.view action)
    (allocated : Preserves Allocated action) : Checked debts locals Safe (liftWGPrefix action) :=
  pair Safe (Passive.native Safe accountSafe action entry) (erasesStatePrefix_lift action) allocated

include accountSafe in
theorem create (key : Key) (psk : Option Key) :
    Checked debts locals Safe (liftWGPrefix (peerCreate key psk)) :=
  StateEnsures.quiet (CompleteAllocated.create Safe accountSafe key psk) (fun _ _ _=>rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ConfigurationAllocated
