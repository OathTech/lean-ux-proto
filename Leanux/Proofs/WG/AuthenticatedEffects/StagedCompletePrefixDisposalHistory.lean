import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixState
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDisposalChecked
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCreateFrames

/-! Logical prefix accounting for the real access events preceding disposal.
The saved accounted state is a history witness, not an inferred native
post-state of an incomplete call. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Disposal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations CompleteCarrier

theorem quiet_cuts (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
    (before : Accounted h ledger debts locals w) (suffix : List Event)
    (births : ∀ event ∈ suffix, birthPackets event = [])
    (terminals : ∀ event ∈ suffix, StagedTerminalComplete.Quiet event) : Cuts Safe h suffix := by
  intro n _bound
  exact accountSafe _ _ _ (before.append_quiet (suffix.take n)
    (fun event member => births event (List.mem_of_mem_take member))
    (fun event member => terminals event (List.mem_of_mem_take member)))

theorem release_access_cuts (peer : Option PeerId) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
    (before : Accounted h ledger debts locals w) (a : Ambient) :
    ∃ suffix, (runWGPrefix (PeerRelease.cut peer) w a h).2 = h ++ suffix ∧ Cuts Safe h suffix := by
  obtain ⟨events,extended⟩ := PeerRelease.cut_history peer w a h
  refine ⟨_,extended,quiet_cuts Safe accountSafe before _ ?_ ?_⟩
  · intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    rfl
  · intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    exact StagedTerminalComplete.Source.peer_access_quiet original

theorem focused_cuts (body : TxDisposition.Obs α) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
    (before : Accounted h ledger debts locals w.wg) :
    ∃ suffix, (runPrefix (QueueHandoff.focused body) w h).2 = h ++ suffix ∧ Cuts Safe h suffix := by
  change ∃ suffix, h ++ _ = h ++ suffix ∧ Cuts Safe h suffix
  refine ⟨_,rfl,quiet_cuts Safe accountSafe before _ ?_ ?_⟩
  · intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    rfl
  · intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    intro position
    rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Disposal
