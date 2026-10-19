import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingExpandedEvidence

/-! Keepalive preparation is followed by the same expanded staging source.
Its actual preparation receipt identifies whether a fresh packet was born;
the resulting ledger is retained through every deeper staging interval. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.KeepaliveExpanded
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier Staging.Points

inductive Point (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List Event) :
    WGWorld → Ambient → List Event → Prop where
  | canonical (point : Staging.Points.Point (keepaliveShape pid) w a h leaf v b last remaining) :
      Point pid w a h v b last
  | staging (prepared : runWGPrefix (CausalJournal.keepalivePrepare pid) w a h=(.ok ((true,u),b),middle))
      (point : StagingExpanded.Point pid u b middle v c last) : Point pid w a h v c last

inductive Evidence (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (pid : PeerId)
    (w : WGWorld) (a : Ambient) (h : List Event) : List Event → WGWorld → Ambient → Prop where
  | canonical (phase : StagingPhase.KeepaliveEvidence h ledger debts locals pid w a last v b) :
      Evidence ledger debts locals pid w a h last v b
  | staging (entered : Ledger)
      (prepared : runWGPrefix (CausalJournal.keepalivePrepare pid) w a h=(.ok ((true,u),b),middle))
      (account : Accounted middle entered debts locals u)
      (change : KeepaliveChange h ledger pid ⟨true,w,u,a,b⟩ entered)
      (phase : StagingExpanded.Evidence entered debts locals last v c) : Evidence ledger debts locals pid w a h last v c

/-- Every declared keepalive cut preserves the same preparation admission
and successor ticket lineage through all expanded staging children. -/
theorem Point.evidence (point : Point pid w a h v b last)
    (before : Accounted h ledger debts locals w) : Evidence ledger debts locals pid w a h last v b := by
  cases point with
  | canonical point=>exact .canonical ((StagingPhase.keepalive_covers before pid a).point point)
  | staging prepared point=>
    obtain ⟨_,_,entered,account,change⟩:=keepalive_entry before prepared
    exact .staging entered prepared account change (point.evidence account)

theorem Point.residual (point : Point pid w a h v b last) :
    ∃remaining,runWGPrefix (Driver.keepaliveObserved hooks pid) w a h=runWGPrefix remaining v b last := by
  cases point with
  | canonical point=>exact ⟨_,point.residual⟩
  | staging prepared point=>exact ⟨_,(keepalivePoint prepared).residual.trans (StagingExpanded.remainder_run point)⟩

noncomputable def remainder (point : Point pid w a h v b last) : WGPrefix Event Unit :=
  Classical.choose point.residual

theorem remainder_run (point : Point pid w a h v b last) :
    runWGPrefix (Driver.keepaliveObserved hooks pid) w a h=runWGPrefix (remainder point) v b last :=
  Classical.choose_spec point.residual

inductive RootPoint (pid : PeerId) (w : World) (h : List Event) : World → List Event → Prop where
  | source (point : Point pid w.wg w.ambient h v b last) : RootPoint pid w h {w with wg:=v,ambient:=b} last

theorem RootPoint.evidence (point : RootPoint pid w h u middle)
    (before : Accounted h ledger debts locals w.wg) :
    Evidence ledger debts locals pid w.wg w.ambient h middle u.wg u.ambient := by
  cases point with
  | source point=>exact point.evidence before

theorem RootPoint.residual (point : RootPoint pid w h u middle) :
    ∃remaining,runPrefix (liftWGObserver (Driver.keepaliveObserved hooks pid)) w h=runPrefix remaining u middle := by
  cases point with
  | source point=>exact ⟨_,StagingComposition.lift_residual w (remainder_run point)⟩

noncomputable def rootRemainder (pid : PeerId) (w : World) (h : List Event)
    (u : World) (middle : List Event) (point : RootPoint pid w h u middle) : PrefixM Event Unit :=
  Classical.choose point.residual

theorem root_remainder_run (point : RootPoint pid w h u middle) :
    runPrefix (liftWGObserver (Driver.keepaliveObserved hooks pid)) w h=
      runPrefix (rootRemainder pid w h u middle point) u middle := Classical.choose_spec point.residual

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.KeepaliveExpanded
