import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryPassive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueued

/-! The source-paired retry-false queued suffix has a bind-compatible contract
without an arbitrary peer-release premise. Its stronger native cut theorem is
the underlying Queued.checked, including the actual successful borrow. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Passive
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal

theorem queued (pid : PeerId) : Checked ledger debts locals
    (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false) := by
  intro w a h entry
  have result := Queued.checked pid entry a
  cases performed : runWGPrefix
      (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false) w a h with
  | mk outcome last =>
    rw [performed] at result
    change runPrefix
      ((HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false).run w) a h = _ at performed
    rw [performed]
    cases outcome with
    | error stop =>
      obtain ⟨rfl,_⟩ := result
      exact ⟨[],by simp,⟨w,entry⟩,True.intro⟩
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      obtain ⟨kept,trace⟩ := result
      have appends : ∃ suffix, last = h ++ suffix := by
        cases trace
        · exact ⟨[],by simp⟩
        · exact ⟨[_],rfl⟩
        · exact ⟨[_],rfl⟩
      obtain ⟨suffix,extended⟩ := appends
      exact ⟨suffix,extended,⟨v,kept⟩,kept⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Passive
