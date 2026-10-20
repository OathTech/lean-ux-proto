import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigRemovalSource

/-! Individual removal enters the existing after-dead account frame only
after the original guard and make-dead source prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

theorem remove_non_null_ordinary (peer : Option PeerId) : Lifecycle.Points.Ordinary (removeNonNullShape peer) := by
  cases peer with
  | none=>exact True.intro
  | some pid=>exact ⟨True.intro,fun _=>Lifecycle.Points.after_dead_ordinary pid⟩

theorem remove_body_ordinary (peer : Option PeerId) : Lifecycle.Points.Ordinary (removeBodyShape peer) := by
  refine ⟨True.intro,?_⟩
  intro absent
  cases absent with
  | false=>exact remove_non_null_ordinary peer
  | true=>exact True.intro

theorem remove_ordinary (peer : Option PeerId) : Lifecycle.Points.Ordinary (removeShape peer) :=
  Lifecycle.Points.Ordinary.source_mpr (remove_factor peer) (remove_body_ordinary peer)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
