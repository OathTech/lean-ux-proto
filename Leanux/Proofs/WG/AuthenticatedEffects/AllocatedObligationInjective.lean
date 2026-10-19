import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationSettlement

/-! Distinct pending tickets cannot name the same allocation-epoch/cell pair.
This is an explicit carrier, separate from residency and ledger-key uniqueness;
its initialized transport and native batch extension are separate obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

def Injective (history : List CausalJournal.Event) (ledger : Ledger) : Prop :=
  ∀ first firstPosition firstOrdinal,
    (first,Status.pending (.allocated firstPosition firstOrdinal)) ∈ ledger →
    ∀ second secondPosition secondOrdinal,
      (second,Status.pending (.allocated secondPosition secondOrdinal)) ∈ ledger →
      ∀ generation id firstValue secondValue,
        Origin history firstPosition firstOrdinal generation id firstValue →
        Origin history secondPosition secondOrdinal generation id secondValue → first = second

/-- The native free's local exclusivity premise follows from pending-cell
injectivity and the chosen ticket's actual allocation, without a whole-run
conservation assumption or an immutable nullable key owner. -/
theorem Injective.exclusive (injective : Injective history ledger)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation skb value)
    (epoch : Packets.epoch w = some generation) : Exclusive history ledger w ticket skb := by
  intro other batch index member otherGeneration otherValue otherOrigin otherEpoch
  have same : otherGeneration = generation := Option.some.inj (otherEpoch.symm.trans epoch)
  subst otherGeneration
  exact injective other batch index member ticket position ordinal pending generation skb otherValue value
    otherOrigin origin

/-- Terminal settlement removes pending entries and cannot create an alias.
This holds for any selected set; its permitted pending-to-terminal Step still
comes from the source caller's existing settlement contract. -/
theorem Injective.settle (injective : Injective history ledger) (chosen : List Ticket)
    (outcome : TransmitSecurity.Staged.Obligations.Terminal) :
    Injective history (settle chosen outcome ledger) := by
  intro first firstPosition firstOrdinal firstMember second secondPosition secondOrdinal secondMember
    generation id firstValue secondValue firstOrigin secondOrigin
  exact injective first firstPosition firstOrdinal (pending_after_settle chosen outcome firstMember).1
    second secondPosition secondOrdinal (pending_after_settle chosen outcome secondMember).1
    generation id firstValue secondValue firstOrigin secondOrigin

theorem injective_empty (history : List CausalJournal.Event) : Injective history [] := by
  intro ticket position ordinal member
  cases member

/-- Derive the actual source free's nonalias condition from the maintained
carrier. The native receipt still determines the physical removal; no packet
is declared disposed merely because its ledger entry became terminal. -/
theorem settle_and_free_injective (receipt : HandshakeSecurity.StagedConservation.Terminal.Receipt)
    (native : receipt.Valid) (valid : Valid births ledger)
    (resident : Resident history ledger receipt.run.before.wg) (injective : Injective history ledger)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation receipt.skb value)
    (outcome : TransmitSecurity.Staged.Obligations.Terminal) :
    let after := settle [ticket] outcome ledger
    TransmitSecurity.Staged.Obligations.Step ledger after ∧ Valid births after ∧ Resident history after receipt.run.after.wg ∧
      Injective history after ∧ (ticket,Status.terminal outcome) ∈ after ∧
      receipt.stamp = (generation,receipt.skb+1) := by
  have actual := (resident ticket position ordinal pending).at_origin origin
  have disposal := settle_and_free receipt native valid resident pending origin
    (injective.exclusive pending origin actual.1) outcome
  exact ⟨disposal.1,disposal.2.1,disposal.2.2.1,injective.settle [ticket] outcome,
    disposal.2.2.2.1,disposal.2.2.2.2.2.1⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
