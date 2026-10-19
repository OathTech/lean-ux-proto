import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseBorrow
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseMutation

/-! Pending queue mutations retain their actual source entry and ordered
obligations. They deliberately do not assert idle accounting in a world
whose native write precedes its existing receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations Staged.Origins CompleteCarrier HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000

structure PendingTake (history : List Event) (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (pid : PeerId) (w : WGWorld) (a : Ambient)
    (peer : Peer) (v : WGWorld) (b : Ambient) : Prop where
  entry : Accounted history ledger debts locals w
  native : ((Take.takePrefix pid).run w).run a=.ok ((some peer,v),b)
  cohort : ∃ generation, Aligned (Born history generation pid peer.internalId)
    (pendingAt (.staged generation pid peer.internalId) ledger) peer.staged
  cleared : Staged.stagedAt v pid=some (peer.internalId,[])
  counter : Staged.dropped v=Staged.dropped w

inductive TakePhase (history : List Event) (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (pid : PeerId) (w : WGWorld) (a : Ambient) :
    List Event → WGWorld → Ambient → Prop where
  | entry (account : Accounted history ledger debts locals w) : TakePhase history ledger debts locals pid w a history w b
  | pending (peer : Peer) (cut : PendingTake history ledger debts locals pid w a peer v b) :
      TakePhase history ledger debts locals pid w a history v b

structure PendingRestore (history : List Event) (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (generation : Nat) (pid : PeerId) (peer : Peer)
    (position : Nat) (w : WGWorld) (a : Ambient) (v : WGWorld) : Prop where
  entry : CompleteSelected.Ready ledger debts locals generation pid peer position history w a
  native : ((Restore.nativeRestore pid peer.staged).run w).run a=.ok (((),v),a)
  cohort : Aligned (Born history generation pid peer.internalId) (pendingAt (.selected position) ledger) peer.staged
  restored : Staged.stagedAt v pid=some (peer.internalId,peer.staged)
  counter : Staged.dropped v=Staged.dropped w

theorem PendingTake.recorded (cut : PendingTake h ledger debts locals pid w a peer v b) :
    ∃ after generation,Staged.Obligations.Step ledger after ∧
      after=transferLocation (.staged generation pid peer.internalId) (.selected h.length) ledger ∧
      CompleteSelected.Ready after debts locals generation pid peer h.length
        (h++[.stagingTaken ⟨pid,⟨some peer,w,v,a,b⟩⟩]) v b :=
  CompleteSelected.taken ⟨pid,⟨some peer,w,v,a,b⟩⟩ cut.native rfl cut.entry

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
