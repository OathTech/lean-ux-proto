import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhasePreparation
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseWhole

/-! Keepalive preparation records its own invocation before entering the same
staging tree. A true result on an existing queue is not a birth. The admitted
successor is named by KeepaliveChange; staging then retains that fixed ledger
through the selected, restored and allocation phases. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations Staged.Origins CompleteCarrier Staging.Points StagingInterior
set_option maxHeartbeats 600000

inductive KeepaliveEvidence (history : List Event) (ledger : Ledger)
    (debts : List AllocatedObligation.CleanupDebt) (locals : List RetirementSecurity.TxLocalBatch)
    (pid : PeerId) (w : WGWorld) (a : Ambient) : List Event → WGWorld → Ambient → Prop where
  | preparation (phase : PreparationPhase history ledger debts locals pid w a middle v b) :
      KeepaliveEvidence history ledger debts locals pid w a middle v b
  | staging (after : Ledger)
      (prepared : runWGPrefix (CausalJournal.keepalivePrepare pid) w a history=(.ok ((true,u),c),entered))
      (account : Accounted entered after debts locals u)
      (change : KeepaliveChange history ledger pid ⟨true,w,u,a,c⟩ after)
      (phase : Evidence after debts locals middle v b) :
      KeepaliveEvidence history ledger debts locals pid w a middle v b

/-- Before the receipt, the inserted native singleton is an alias awaiting
its exact fresh birth position. The old cohort is empty and the counter is
unchanged; the native full preparation follows the same hidden choices. -/
theorem pending_birth_facts (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some peer) (empty : peer.staged.isEmpty=true)
    (allocated : keepaliveAllocation.run (clock a .keepaliveStagedEmpty true)=.ok (false,b)) :
    let v:=queueWorld pid peer (peer.staged++[{mtu:=d.mtu}]) d w
    let event:=keepaliveEvent pid true w v a b
    ((RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid).run w).run a=.ok ((true,v),b) ∧
      pendingAt (.staged d.ifindex pid peer.internalId) ledger=[] ∧
      Staged.stagedAt v pid=some (peer.internalId,[{mtu:=d.mtu}]) ∧
      Staged.dropped v=Staged.dropped w ∧
      Born (h++[event]) d.ifindex pid peer.internalId ⟨h.length,0⟩ {mtu:=d.mtu} ∧
      births (h++[event])=births h++[⟨h.length,0⟩] := by
  obtain ⟨_,native,cohort,physical,counter⟩:=keepalive_pending before device resident empty allocated
  exact ⟨native,cohort,physical,counter,(keepalive_birth device resident empty allocated).2,
    keepalive_tickets device resident empty allocated⟩

theorem keepalive_covers (before : Accounted h ledger debts locals w) (pid : PeerId) (a : Ambient) :
    Covers (KeepaliveEvidence h ledger debts locals pid w a) (keepaliveShape pid) w a h := by
  unfold keepaliveShape
  change Covers _ (.bind (preparationShape pid) _) w a h
  have preparation:=preparation_covers before pid a
  apply covers_bind (preparation.mono (fun _ _ _ phase=>.preparation phase))
  intro ready u b middle prepared
  cases ready <;> dsimp only
  · exact .preparation (preparation.normal prepared)
  · obtain ⟨_,_,after,account,change⟩:=CompleteKeepalive.normal pid before a b u middle true prepared
    exact (staging_covers account pid b).mono (fun _ _ _ phase=>.staging after prepared account change phase)

/-- Every canonical keepalive/staging point is derived from the original
account and retains the original remainder, without assuming normal return. -/
theorem keepalive_every_point (before : Accounted h ledger debts locals w)
    (point : Point (keepaliveShape pid) w a h leaf v b middle remaining) :
    KeepaliveEvidence h ledger debts locals pid w a middle v b ∧
      runWGPrefix (Driver.keepaliveObserved hooks pid) w a h=runWGPrefix remaining v b middle :=
  ⟨(keepalive_covers before pid a).point point,point.residual⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
