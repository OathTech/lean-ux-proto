import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseFront
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseCleanup

/-! The actual creation tail either retains its accepted phase or repays
references before visiting the original refusal cohort in order. Each branch
is derived from its real native guard, with no assumed whole-tree coverage. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
open HandshakeSecurity.StagedDisposal CreatePoints
set_option maxHeartbeats 600000

theorem tail_unpublished (first : SkbId) (ret : Int)
    (steps : Staged.Obligations.Step rootLedger ledger) (pending : PendingBatch h ledger items)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg) :
    Covers (fun h w=>Live rootLedger debts locals pid items h w.wg) (tailShape pid items first ret) w h := by
  unfold tailShape
  apply covers_marked
  have okSafe:=atom_covers (.branch .createDataOk (ret == 0)) trivial (.unpublished ledger steps pending before)
  apply covers_bind okSafe
  intro ok u middle tested
  obtain ⟨_,rfl,atPipe⟩:=guard_account .createDataOk (ret == 0) before tested
  cases ok with
  | true=>exact covers_pure _ (okSafe.normal tested)
  | false=>
    have pipeSafe:=atom_covers (.branch .createDataOkEpipe (ret == -WG.EPIPE)) trivial (okSafe.normal tested)
    apply covers_bind pipeSafe
    intro pipe v last piped
    obtain ⟨_,rfl,atRead⟩:=guard_account .createDataOkEpipe (ret == -WG.EPIPE) atPipe piped
    cases pipe with
    | true=>exact covers_pure _ (pipeSafe.normal piped)
    | false=>
      have readSafe:=atom_covers (.packet first) trivial (pipeSafe.normal piped)
      apply covers_bind readSafe
      intro packet q readHistory read
      obtain ⟨atKey,suffix,grown⟩:=access_account _ _ (getTxSkbPrefix_erases first) (packet_view first) atRead read
      have atKeyPending : PendingBatch readHistory ledger items := grown ▸ pending.append suffix
      have keySafe:=covers_child (.repay (some packet.keypair)) (readSafe.normal read)
        (fun _ _ _ run=>passive_child (.repay (some packet.keypair)) trivial (readSafe.normal read) run)
      apply covers_bind keySafe
      intro ignored r keyHistory repaid
      obtain ⟨atPeer,keySuffix,keyGrown⟩:=access_account _ _ (keypairPutPrefix_erases _ _)
        (KeyFrames.put (some packet.keypair) false) atKey repaid
      have atPeerPending : PendingBatch keyHistory ledger items := keyGrown ▸ atKeyPending.append keySuffix
      have releaseSafe:=release_covers (some pid) (keySafe.normal repaid)
      apply covers_bind releaseSafe
      intro ignored finalWorld finalHistory released
      cases ignored
      obtain ⟨next,releaseSuffix,step,frame,releaseGrown,atFree⟩:=release_account (some pid) atPeer released
      have atFreePending : PendingBatch finalHistory next items :=
        releaseGrown ▸ (atPeerPending.allocated_frame frame).append releaseSuffix
      exact cleanup_covers (steps.trans step) (done:=[]) rfl
        (fun _ member=>False.elim (List.not_mem_nil member)) atFreePending atFree

theorem tail_accepted (first : SkbId) (ret : Int) (code : ret=0 ∨ ret = -WG.EPIPE)
    (before : Live rootLedger debts locals pid items h w.wg) :
    Covers (fun h w=>Live rootLedger debts locals pid items h w.wg) (tailShape pid items first ret) w h := by
  unfold tailShape
  apply covers_marked
  have okSafe:=atom_covers (.branch .createDataOk (ret == 0)) trivial before
  apply covers_bind okSafe
  intro ok u middle tested
  have okValue:=guard_value .createDataOk (ret == 0) before tested
  cases ok with
  | true=>exact covers_pure _ (okSafe.normal tested)
  | false=>
    have retPipe : ret = -WG.EPIPE := by
      rcases code with rfl | pipe
      · cases okValue
      · exact pipe
    have pipeSafe:=atom_covers (.branch .createDataOkEpipe (ret == -WG.EPIPE)) trivial (okSafe.normal tested)
    apply covers_bind pipeSafe
    intro pipe v last piped
    have pipeValue:=guard_value .createDataOkEpipe (ret == -WG.EPIPE) (okSafe.normal tested) piped
    have yes : pipe=true := by simpa only [retPipe,BEq.rfl] using pipeValue
    cases yes
    exact covers_pure _ (pipeSafe.normal piped)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
