import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteFrontSource

/-! The front's paired normal and stopped cuts are exposed in the same
bind-compatible carrier used by subsequent staging and peer repayment. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteFront
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity CausalJournal Staged.Obligations StagedAdmission.Front CompleteCarrier

theorem checked (input : Input) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h) :
    StatePrefixPreserves (Carrier debts locals) Safe
      (CausalJournal.front input.family input.address input.packets input.mtu) := by
  intro w ambient history before
  obtain ⟨ledger,accounted⟩ := before
  obtain ⟨suffix,extended,_,_⟩ := StagedAdmission.Front.front_checked
    (coreEntry accounted.entry.core) input rfl w ambient history ⟨rfl,rfl⟩
  cases performed : runWGPrefix
      (CausalJournal.front input.family input.address input.packets input.mtu) w ambient history with
  | mk outcome last =>
    change runPrefix ((CausalJournal.front input.family input.address input.packets input.mtu).run w)
      ambient history = _ at performed
    rw [performed] at extended ⊢
    cases outcome with
    | error stop =>
      obtain ⟨after,snapshot,_,next,_,_⟩ := front_stopped input accounted ambient last stop performed
      exact ⟨suffix,extended,accountSafe _ _ _ next,True.intro⟩
    | ok out =>
      obtain ⟨⟨value,v⟩,clock⟩ := out
      obtain ⟨after,next,_⟩ := front_normal input accounted ambient clock v last value performed
      exact ⟨suffix,extended,accountSafe _ _ _ next,after,next⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteFront
