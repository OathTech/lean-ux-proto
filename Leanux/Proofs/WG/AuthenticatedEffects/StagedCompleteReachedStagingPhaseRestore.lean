import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseTake

/-! Restoration has three semantic phases: the selected entry, its literal
prepend write awaiting the existing receipt, and the restored idle account.
The original ordered cohort and unchanged drop counter are retained. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations Staging.Points CompleteCarrier HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000
attribute [local implicit_reducible] Native.action Restore.nativeRestore

inductive RestorePhase (history : List Event) (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (generation : Nat) (pid : PeerId) (peer : Peer)
    (position : Nat) (w : WGWorld) (a : Ambient) : List Event → WGWorld → Ambient → Prop where
  | entry (ready : CompleteSelected.Ready ledger debts locals generation pid peer position history w a) :
      RestorePhase history ledger debts locals generation pid peer position w a history w a
  | pending (cut : PendingRestore history ledger debts locals generation pid peer position w a v) :
      RestorePhase history ledger debts locals generation pid peer position w a history v a
  | recorded (native : ((Restore.nativeRestore pid peer.staged).run w).run a=.ok (((),v),a))
      (account : Accounted (history++[.stagedRestored ⟨pid,peer.staged,⟨(),w,v,a,a⟩⟩])
        (HeldFrontier.restoredLedger ledger generation pid peer position) debts locals v)
      (ordered : pendingAt (.staged generation pid peer.internalId)
        (HeldFrontier.restoredLedger ledger generation pid peer position)=pendingAt (.selected position) ledger)
      (counter : Staged.dropped v=Staged.dropped w) :
      RestorePhase history ledger debts locals generation pid peer position w a
        (history++[.stagedRestored ⟨pid,peer.staged,⟨(),w,v,a,a⟩⟩]) v a

theorem restore_covers
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    Covers (RestorePhase h ledger debts locals generation pid peer position w a)
      (restoreShape pid peer.staged) w a h := by
  unfold restoreShape
  change Covers _ (.receipt _ _) w a h
  constructor
  · erw [covers_mpr (by first | rfl | (simp only [Restore.nativeRestore,lift_bind]))]
    have first : Covers (RestorePhase h ledger debts locals generation pid peer position w a)
        (.native (.peer pid)) w a h := by
      refine ⟨.entry before,?_⟩
      intro cached u b middle run
      obtain ⟨rfl,rfl,rfl,_⟩:=peer_success run
      exact .entry before
    apply covers_bind first
    intro cached u b middle firstRun
    obtain ⟨worldEq,clockEq,historyEq,d,device,resident⟩:=peer_success firstRun
    subst u
    subst b
    subst middle
    apply covers_bind first
    intro queued v c last secondRun
    obtain ⟨worldEq,clockEq,historyEq,e,device',resident'⟩:=peer_success secondRun
    subst v
    subst c
    subst last
    have equalDevice : e=d:=Option.some.inj (device'.symm.trans device)
    subst e
    have equalPeer : queued=cached:=Option.some.inj (resident'.symm.trans resident)
    subst queued
    refine ⟨.entry before,?_⟩
    intro value q later events performed
    obtain ⟨native,rfl⟩:=lift_success performed
    have written:=StagingInterior.restore_write (pid:=pid) (p:=cached) (packets:=peer.staged) (a:=a) device
    change ((WG.setPeer pid {cached with staged:=peer.staged++cached.staged}).run w).run a=_ at written
    erw [written] at native
    cases native
    obtain ⟨run,cohort,restored,counter⟩:=StagingInterior.restore_pending before device resident
    exact .pending ⟨before,run,cohort,restored,counter⟩
  · intro value v b middle performed
    obtain ⟨native,rfl⟩:=lift_success performed
    obtain ⟨d,current,device,resident,_,_⟩:=StagingInterior.restore_ready_total before
    have actual:=StagingInterior.restore_native (packets:=peer.staged) (a:=a) device resident
    erw [actual] at native
    cases native
    obtain ⟨account,_,ordered,counter⟩:=StagingInterior.restore_accounted before device resident
    exact .recorded actual account ordered counter

theorem restore_point
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a)
    (point : Point (restoreShape pid peer.staged) w a h leaf v b middle remaining) :
    RestorePhase h ledger debts locals generation pid peer position w a middle v b ∧
      runWGPrefix (CausalJournal.stagedRestore pid peer.staged) w a h=runWGPrefix remaining v b middle :=
  ⟨(restore_covers before).point point,point.residual⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
