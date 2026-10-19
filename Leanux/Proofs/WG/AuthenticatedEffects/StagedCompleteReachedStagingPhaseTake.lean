import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseNative

/-! Every canonical take point keeps the original complete entry or the
exact cleared-but-unrecorded cohort. The receipt then transfers those same
tickets to the selected location; it does not create a replacement cohort. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations Staging.Points CompleteCarrier HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000
attribute [local implicit_reducible] Native.action Take.takePrefix

theorem take_covers (before : Accounted h ledger debts locals w) (pid : PeerId) (a : Ambient) :
    Covers (TakePhase h ledger debts locals pid w a) (takeShape pid) w a h := by
  unfold takeShape
  dsimp only [Covers,id]
  erw [covers_mpr (lift_bind _ _)]
  have read : Covers (TakePhase h ledger debts locals pid w a) (.native (.peer pid)) w a h := by
    refine ⟨.entry before,?_⟩
    intro peer u b middle run
    obtain ⟨rfl,rfl,rfl,_⟩:=peer_success run
    exact .entry before
  apply covers_bind read
  intro peer u b middle readRun
  obtain ⟨worldEq,clockEq,historyEq,d,device,resident⟩:=peer_success readRun
  subst u
  subst b
  subst middle
  erw [covers_mpr (lift_bind _ _)]
  have guard : Covers (TakePhase h ledger debts locals pid w a)
      (.native (.branch .stagedEmpty peer.staged.isEmpty)) w a h := by
    refine ⟨.entry before,?_⟩
    intro value u b middle run
    obtain ⟨_,rfl,_,rfl⟩:=branch_success run
    exact .entry before
  apply covers_bind guard
  intro empty u b middle branchRun
  cases empty <;> dsimp only
  · obtain ⟨value,worldEq,clockEq,historyEq⟩:=branch_success branchRun
    subst u
    subst b
    subst middle
    have nonempty : peer.staged.isEmpty=false:=value.symm
    erw [covers_mpr (lift_bind _ _)]
    have written : Covers (TakePhase h ledger debts locals pid w a)
        (.native (.setPeer pid {peer with staged:=[]})) w (StagingInterior.clock a .stagedEmpty peer.staged.isEmpty) h := by
      refine ⟨.entry before,?_⟩
      intro value v c last performed
      obtain ⟨native,rfl⟩:=lift_success performed
      have actual:=StagingInterior.take_write (pid:=pid) (p:=peer) (a:=StagingInterior.clock a .stagedEmpty peer.staged.isEmpty) device
      change ((WG.setPeer pid {peer with staged:=[]}).run w).run _=_ at actual
      erw [actual] at native
      cases native
      obtain ⟨take,aligned,cleared,counter⟩:=StagingInterior.take_pending before device resident nonempty (a:=a)
      apply TakePhase.pending peer
      exact ⟨before,by simpa only [nonempty] using take,⟨d.ifindex,aligned⟩,cleared,counter⟩
    apply covers_bind written
    intro value v c last performed
    exact written.normal performed
  · exact guard.normal branchRun

theorem take_point (before : Accounted h ledger debts locals w)
    (point : Point (takeShape pid) w a h leaf v b middle remaining) :
    TakePhase h ledger debts locals pid w a middle v b ∧
      runWGPrefix (liftWGPrefix (Take.takePrefix pid)) w a h=runWGPrefix remaining v b middle :=
  ⟨(take_covers before pid a).point point,point.residual⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
