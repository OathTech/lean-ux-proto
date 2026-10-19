import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPointCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPointResidual

/-! The rejected guard path reaches the original invalidation/repayment
prefix, then the actual restore receipt and queued-initiation child. The
same selected ledger supplies the destination; no idle carrier is asserted
before restoration is recorded. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity CausalJournal
open Staged.Obligations HandshakeSecurity.StagedConservation CompleteCarrier
set_option maxHeartbeats 600000

def rejectedTail (pid : PeerId) (peer : Peer) : WGPrefix Event Unit := do
  CausalJournal.stagedRestore pid peer.staged
  HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false

theorem rejection_factor (pid : PeerId) (peer : Peer) (key : Option KeypairId) (invalid : Bool) :
    HeldSource.noKey pid peer key invalid=
      (RestoreEntry.prefixWith (m:=WGPrefix Event) liftWGPrefix peer.staged key invalid >>= fun _=>rejectedTail pid peer) := by
  unfold HeldSource.noKey rejectedTail
  exact RestoreEntry.no_key_factor effects CausalJournal.stagedRestore
    (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease) pid peer.staged key invalid

structure Restored (history : History) (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (pid : PeerId) (w : WGWorld) (a : Ambient)
    (peer : Peer) (generation position : Nat) (key : Option KeypairId) (invalid : Bool)
    (h : History) (v : WGWorld) (b : Ambient) where
  nativeWorld : WGWorld
  nativeClock : Ambient
  nativeHistory : History
  prefixRun : runWGPrefix (RestoreEntry.prefixWith (m:=WGPrefix Event) liftWGPrefix peer.staged key invalid) v b h=
    (.ok (((),nativeWorld),nativeClock),nativeHistory)
  selected : CompleteSelected.Ready ledger debts locals generation pid peer position
    nativeHistory nativeWorld nativeClock
  receipt : Restore.Receipt
  peerEq : receipt.pid=pid
  packetsEq : receipt.packets=peer.staged
  beforeEq : receipt.run.before=nativeWorld
  clockEq : receipt.run.ambientBefore=nativeClock
  native : receipt.Valid
  restored : runWGPrefix (CausalJournal.stagedRestore pid peer.staged) nativeWorld nativeClock nativeHistory=
    (.ok (((),receipt.run.after),receipt.run.ambientAfter),nativeHistory++[.stagedRestored receipt])
  accounted : Accounted (nativeHistory++[.stagedRestored receipt])
    (HeldFrontier.restoredLedger ledger generation pid peer position) debts locals receipt.run.after
  ordered : pendingAt (.staged generation pid peer.internalId)
      (HeldFrontier.restoredLedger ledger generation pid peer position)=pendingAt (.selected position) ledger
  counter : Staged.dropped receipt.run.after=Staged.dropped nativeWorld
  continuation : runWGPrefix (Driver.stagingObserved hooks pid) w a history=
    runWGPrefix (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false)
      receipt.run.after receipt.run.ambientAfter (nativeHistory++[.stagedRestored receipt])

/-- The actual failed prefix retains its selected receipt anchor. A normal
prefix supplies the resident restore cut itself and the original queued
continuation, whether that continuation later returns or stops. -/
theorem rejected_cases
    (path : CallbackPath history original debts locals pid w a peer keypair selectedHistory
      selectedWorld selectedClock ledger generation (.rejected key invalid) h v b) :
    (∃ stop last,
      runWGPrefix (RestoreEntry.prefixWith (m:=WGPrefix Event) liftWGPrefix peer.staged key invalid) v b h=(.error stop,last) ∧
      CompleteSelected.Active ledger debts generation pid peer history.length last ∧
      runWGPrefix (Driver.stagingObserved hooks pid) w a history=(.error stop,last)) ∨
    Nonempty (Restored history ledger debts locals pid w a peer generation history.length key invalid h v b) := by
  have rule := CompleteSelected.before_restore (ledger:=ledger) (debts:=debts) (locals:=locals)
    (generation:=generation) (pid:=pid) (peer:=peer) (position:=history.length)
    (fun _=>id) peer.staged key invalid
  cases prefixRun : runWGPrefix (RestoreEntry.prefixWith (m:=WGPrefix Event) liftWGPrefix peer.staged key invalid) v b h with
  | mk outcome last=>
    cases outcome with
    | error stop=>
      obtain ⟨_,_,active,_⟩:=rule v b h path.ready
      change CompleteSelected.Active ledger debts generation pid peer history.length
        (runWGPrefix (RestoreEntry.prefixWith (m:=WGPrefix Event) liftWGPrefix peer.staged key invalid) v b h).2 at active
      rw [prefixRun] at active
      refine Or.inl ⟨stop,last,rfl,active,?_⟩
      rw [path.continuation]
      change runWGPrefix (HeldSource.noKey pid peer key invalid) v b h=_
      rw [rejection_factor,run_bind,prefixRun]
    | ok out=>
      obtain ⟨⟨ignored,u⟩,c⟩:=out
      cases ignored
      have selected := Staging.normal rule path.ready prefixRun
      obtain ⟨d,current,device,resident,restoreRun,accounted⟩:=StagingInterior.restore_ready_total selected
      let restoredWorld := StagingInterior.queueWorld pid current (peer.staged++current.staged) d u
      let receipt : Restore.Receipt:=⟨pid,peer.staged,⟨(),u,restoredWorld,c,c⟩⟩
      have facts:=StagingInterior.restore_accounted selected device resident
      refine Or.inr ⟨{
        nativeWorld:=u,nativeClock:=c,nativeHistory:=last,prefixRun:=prefixRun,selected:=selected,
        receipt:=receipt,peerEq:=rfl,packetsEq:=rfl,beforeEq:=rfl,clockEq:=rfl,
        native:=StagingInterior.restore_native device resident,restored:=restoreRun,accounted:=accounted,
        ordered:=facts.2.2.1,counter:=facts.2.2.2,continuation:=?_}⟩
      rw [path.continuation]
      change runWGPrefix (HeldSource.noKey pid peer key invalid) v b h=_
      rw [rejection_factor,run_bind,prefixRun]
      dsimp only
      unfold rejectedTail
      rw [run_bind,restoreRun]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
