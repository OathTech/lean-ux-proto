import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPhysical

/-! Physical and immutable history projections are transported separately.
The history projection remains meaningful after native exceptions erase the
returned World; no stopped physical ownership is inferred from it. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

theorem Physical.recorded (physical : Physical history ledger debts w) : Recorded history ledger debts := by
  intro ticket position ordinal tracked
  obtain ⟨generation,id,value,origin,_,_⟩ := tracked.backed physical.resident physical.cleanup
  exact ⟨generation,id,value,origin⟩

theorem Recorded.append (recorded : Recorded history ledger debts) (suffix : List CausalJournal.Event) :
    Recorded (history ++ suffix) ledger debts := by
  intro ticket position ordinal tracked
  obtain ⟨generation,id,value,origin⟩ := recorded ticket position ordinal tracked
  exact ⟨generation,id,value,origin.append suffix⟩

theorem Recorded.mixed_append (recorded : Recorded history ledger debts)
    (mixed : MixedInjective history ledger debts) (suffix : List CausalJournal.Event) :
    MixedInjective (history ++ suffix) ledger debts := by
  intro first fp fo firstTracked second sp so secondTracked generation id firstValue secondValue
    firstOrigin secondOrigin
  obtain ⟨_,_,_,firstPrior⟩ := recorded first fp fo firstTracked
  obtain ⟨_,_,_,secondPrior⟩ := recorded second sp so secondTracked
  exact mixed first fp fo firstTracked second sp so secondTracked generation id firstValue secondValue
    (firstOrigin.prefix firstPrior.position_lt) (secondOrigin.prefix secondPrior.position_lt)

theorem Physical.append (physical : Physical history ledger debts w) (suffix : List CausalJournal.Event) :
    Physical (history ++ suffix) ledger debts w :=
  ⟨physical.resident.append suffix,physical.covered.append suffix,physical.cleanup.append suffix,
    physical.recorded.mixed_append physical.mixed suffix⟩

theorem Physical.views (physical : Physical history ledger debts w)
    (epoch : Packets.epoch v = Packets.epoch w)
    (cells : PacketMaterial.view v = PacketMaterial.view w) : Physical history ledger debts v :=
  ⟨fun _ _ _ member => (physical.resident _ _ _ member).views epoch cells,
    physical.covered.views epoch cells,physical.cleanup.views epoch cells,physical.mixed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
