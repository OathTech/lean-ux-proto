import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDisposalHistory

/-! The actual nested release first emits native peer accesses, then its
counted receipt, and finally a history-preserving native finish. Each cut
keeps the paired ledger without treating final release as quiet. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Disposal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations CompleteCarrier

theorem nested_cuts (peer : Option PeerId) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
    (w : World) (h : List Event) (before : Carrier debts locals h w.wg w.ambient) :
    ∃ suffix, (runPrefix (Admission.actualOps.release peer) w h).2 = h ++ suffix ∧ Cuts Safe h suffix := by
  obtain ⟨ledger,accounted⟩ := before
  obtain ⟨_,_,finished,_⟩ := CompleteSource.nested peer Safe accountSafe w h ⟨ledger,accounted⟩
  obtain ⟨access,extended,cuts⟩ := release_access_cuts peer Safe accountSafe accounted w.ambient
  rw [PeerRelease.actual_run] at finished ⊢
  cases performed : runWGPrefix (PeerRelease.cut peer) w.wg w.ambient h with
  | mk outcome last =>
    rw [performed] at extended finished
    change last = h ++ access at extended
    cases outcome with
    | error stop => exact ⟨access,extended,cuts⟩
    | ok out =>
      obtain ⟨⟨value,g⟩,ambient⟩ := out
      have same := PeerRelease.finish_history value {w with wg := g,ambient := ambient}
        (last ++ [PeerRelease.receipt peer value w.wg g w.ambient ambient])
      rw [same] at finished ⊢
      rw [extended] at finished ⊢
      exact ⟨access ++ [_],by simp only [List.append_assoc],
        cuts.append (Cuts.singleton cuts.last finished)⟩

theorem nested (peer : Option PeerId) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h) :
    Ensures (fun h w => Carrier debts locals h w.wg w.ambient) Safe
      (Admission.actualOps.release peer) (fun _ h w => Carrier debts locals h w.wg w.ambient) :=
  Ensures.of_cuts (CompleteSource.nested peer Safe accountSafe) (nested_cuts peer Safe accountSafe)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Disposal
