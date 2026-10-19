import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNestedPeerContinuation

/-! Native final peer erasure precedes its existing lifetime receipt.
The following marker uses the slot captured at that original erase and
leaves the world unchanged; the counted receipt still names the whole call. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NestedPeer
open Leanux Leanux.WG Leanux.Proofs.Logged
open CausalJournal AllocatedObligation PeerRetirement HandshakeSecurity.StagedDisposal

def erasedWorld (pid : PeerId) (dropped : Nat) (w : WGWorld) : WGWorld :=
  {w with dev:=w.dev.map fun d=>{d with txDropped:=d.txDropped+dropped,peers:=d.peers.erase pid}}

def eraseEvents (w : WGWorld) (pid : PeerId) : List CausalJournal.Event :=
  match (Peers.snapshot w).slots pid with
  | none=>[]
  | some stamp=>[TxSource.peerEncode txEvent (.release pid stamp)]

def eraseMarker (w : WGWorld) (pid : PeerId) : WGPrefix CausalJournal.Event Unit :=
  match (Peers.snapshot w).slots pid with
  | none=>pure ()
  | some stamp=>emitStatePrefix (TxSource.peerEncode txEvent (.release pid stamp))

theorem erase_native (pid : PeerId) (dropped : Nat) (w : WGWorld) (a : Ambient) :
    ((modifyDev fun d=>{d with txDropped:=d.txDropped+dropped,peers:=d.peers.erase pid}).run w).run a=
      .ok (((),erasedWorld pid dropped w),a) := rfl

theorem marker_run (origin w : WGWorld) (pid : PeerId) (a : Ambient) (h : List CausalJournal.Event) :
    runWGPrefix (eraseMarker origin pid) w a h=(.ok (((),w),a),h++eraseEvents origin pid) := by
  unfold eraseMarker eraseEvents
  cases (Peers.snapshot origin).slots pid <;> simp only [List.append_nil] <;> rfl

theorem erase_run (pid : PeerId) (dropped : Nat) (w : WGWorld) (a : Ambient) (h : List CausalJournal.Event) :
    runWGPrefix (actual.erase pid dropped) w a h=
      (.ok (((),erasedWorld pid dropped w),a),h++eraseEvents w pid) := by
  let events : List Peers.PeerEvent:=match (Peers.snapshot w).slots pid with
    | none=>[] | some stamp=>[.release pid stamp]
  have raw (history : List Peers.PeerEvent) :
      runWGPrefix (Peers.erasePeerPrefix pid dropped) w a history=
        (.ok (((),erasedWorld pid dropped w),a),history++events) := by
    rw [runWGPrefix,Peers.erasePeerPrefix_run,erase_native]
    dsimp only [events]
    cases (Peers.snapshot w).slots pid <;> simp only [List.append_nil] <;> rfl
  have focused:=focusPrefix_suffix (TxSource.peerEncode txEvent) (TxSource.peerDecode txEvent?)
    ((Peers.erasePeerPrefix pid dropped).run w) a h (.ok (((),erasedWorld pid dropped w),a)) events (raw _)
  change runPrefix (focusPrefix (TxSource.peerEncode txEvent) (TxSource.peerDecode txEvent?)
    ((Peers.erasePeerPrefix pid dropped).run w)) a h=_
  rw [focused]
  dsimp only [events,eraseEvents]
  cases (Peers.snapshot w).slots pid <;> rfl

theorem erased_cut
    (checked : runWGPrefix (prefixAt actual .checked peer) w a h=(.ok ((some (pid,p),v),b),middle)) :
    runWGPrefix (PeerRelease.cut peer) w a h=
      (.ok ((some (pid,p),erasedWorld pid p.staged.length v),b),middle++eraseEvents v pid) := by
  rw [PeerRelease.cut,factor .checked]
  change runStatePrefix _ w a h=_
  change runStatePrefix _ w a h=_ at checked
  rw [runStatePrefix_bind,checked]
  change runWGPrefix (do actual.erase pid p.staged.length;pure (some (pid,p))) v b middle=_
  rw [runWGPrefix,runStatePrefix_bind]
  have erased:=erase_run pid p.staged.length v b middle
  change runStatePrefix _ _ _ _=_ at erased
  rw [erased]
  rfl

theorem erased_residual
    (checked : runWGPrefix (prefixAt actual .checked peer) w.wg w.ambient h=(.ok ((some (pid,p),v),b),middle)) :
    runPrefix (Admission.actualOps.release peer) w h=
      runPrefix (resume peer w (do eraseMarker v pid;pure (some (pid,p))))
        {w with wg:=erasedWorld pid p.staged.length v,ambient:=b} middle := by
  rw [PeerRelease.actual_run,erased_cut checked,resume_run]
  have marker:=marker_run v (erasedWorld pid p.staged.length v) pid b middle
  simp only [runWGPrefix,runStatePrefix_bind] at marker ⊢
  rw [marker]
  rfl

def pendingRecords (peer : Option PeerId) (pid : PeerId) (p : Peer) (origin : World)
    (beforeErase : WGWorld) (clock : Ambient) : PrefixM CausalJournal.Event Unit := do
  liftWGObserver (eraseMarker beforeErase pid)
  emitPrefix (PeerRelease.receipt peer (some (pid,p)) origin.wg
    (erasedWorld pid p.staged.length beforeErase) origin.ambient clock)

/-- Both actual outstanding records complete without a native mutation or
failure. Their counted receipt retains the original whole-release entry. -/
theorem records_run (peer : Option PeerId) (pid : PeerId) (p : Peer) (origin : World)
    (beforeErase : WGWorld) (clock : Ambient) (h : List CausalJournal.Event) :
    let target:={origin with wg:=erasedWorld pid p.staged.length beforeErase,ambient:=clock}
    runPrefix (pendingRecords peer pid p origin beforeErase clock) target h=
      (.ok ((),target),h++eraseEvents beforeErase pid++[PeerRelease.receipt peer (some (pid,p))
        origin.wg target.wg origin.ambient clock]) := by
  dsimp only
  rw [pendingRecords,runPrefix_bind,liftWGObserver_run,marker_run]
  rfl

theorem erased_records_residual
    (checked : runWGPrefix (prefixAt actual .checked peer) w.wg w.ambient h=(.ok ((some (pid,p),v),b),middle)) :
    runPrefix (Admission.actualOps.release peer) w h=
      runPrefix (do pendingRecords peer pid p w v b;PeerRelease.finish (some (pid,p)))
        {w with wg:=erasedWorld pid p.staged.length v,ambient:=b} middle := by
  rw [PeerRelease.actual_run,erased_cut checked,runPrefix_bind,records_run]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NestedPeer
