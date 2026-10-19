import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationInjective

/-! Existing allocated positions remain within the original history. This
bound is derived from their actual resident origins before extending history;
without it, appending could supply previously missing future allocations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations
variable {id : Nat}

theorem Origin.prefix (origin : Origin (history ++ suffix) position ordinal generation id value)
    (earlier : position < history.length) : Origin history position ordinal generation id value := by
  obtain ⟨packets,run,packet,atPosition,valid,epoch,payload,cell,material⟩ := origin
  exact ⟨packets,run,packet,by simpa [List.getElem?_append_left earlier] using atPosition,
    valid,epoch,payload,cell,material⟩

theorem Resident.position_lt (resident : Resident history ledger w)
    (member : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger) :
    position < history.length := by
  obtain ⟨_,_,_,origin,_,_⟩ := resident ticket position ordinal member
  exact origin.position_lt

theorem Injective.append (injective : Injective history ledger)
    (resident : Resident history ledger w) (suffix : List CausalJournal.Event) :
    Injective (history ++ suffix) ledger := by
  intro first firstPosition firstOrdinal firstMember second secondPosition secondOrdinal secondMember
    generation id firstValue secondValue firstOrigin secondOrigin
  exact injective first firstPosition firstOrdinal firstMember second secondPosition secondOrdinal secondMember
    generation id firstValue secondValue
    (firstOrigin.prefix (resident.position_lt firstMember))
    (secondOrigin.prefix (resident.position_lt secondMember))

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
