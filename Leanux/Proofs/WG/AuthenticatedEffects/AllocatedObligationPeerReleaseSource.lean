import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationAdmissionSource

/-! The actual nested TX peer-release cut and its continuation. The existing
counted receipt is emitted before final-release timer checks or retirement;
all earlier peer access events and the first stopped result remain intact. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.PeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open HandshakeSecurity.StagedDisposal
set_option pp.structureInstances false

def ops : PeerSource.Ops (WGPrefix CausalJournal.Event) :=
  PeerSource.Ops.focus (TxSource.peerEncode CausalJournal.txEvent)
    (TxSource.peerDecode CausalJournal.txEvent?) PeerSource.peers

def cut (peer : Option PeerId) : WGPrefix CausalJournal.Event (Option (PeerId × Peer)) :=
  PeerSource.cutWith ops peer

def finish (value : Option (PeerId × Peer)) : PrefixM CausalJournal.Event Unit :=
  match value with
  | none => pure ()
  | some (pid,p) => liftWGObserver (ops.step (releaseFinish pid p))

def receipt (peer : Option PeerId) (value : Option (PeerId × Peer))
    (w v : WGWorld) (a b : Ambient) : CausalJournal.Event :=
  .stagedDisposal (.release peer ⟨value,w,v,a,b⟩)

/-- Exact execution equation for the actual nested release. A successful
counted cut records its result before the suffix, including when that suffix
stops. A failed cut emits no fabricated counted receipt. -/
theorem actual_run (peer : Option PeerId) (w : World) (history : List CausalJournal.Event) :
    runPrefix (Admission.actualOps.release peer) w history =
      match runWGPrefix (cut peer) w.wg w.ambient history with
      | (.error stop,last) => (.error stop,last)
      | (.ok ((value,g),ambient),last) =>
        runPrefix (finish value) {w with wg := g,ambient := ambient}
          (last ++ [receipt peer value w.wg g w.ambient ambient]) := by
  change runPrefix (liftWGObserver (PeerSource.observed ops CausalJournal.Event.stagedDisposal peer)) w history = _
  rw [liftWGObserver_run]
  unfold PeerSource.observed
  simp only [runWGPrefix]
  rw [runStatePrefix_bind]
  have captured := runWGPrefix_receiptWGObserved (cut peer)
    (fun r => CausalJournal.Event.stagedDisposal (.release peer r)) w.wg w.ambient history
  simp only [runWGPrefix] at captured
  simp only [cut] at captured ⊢
  rw [captured]
  cases performed : runStatePrefix (PeerSource.cutWith ops peer) w.wg w.ambient history with
  | mk outcome last =>
    cases outcome with
    | error stop => rfl
    | ok out =>
      obtain ⟨⟨value,g⟩,ambient⟩ := out
      cases value with
      | none => rfl
      | some pair => rfl

theorem after_cut (peer : Option PeerId)
    (performed : runWGPrefix (cut peer) w.wg w.ambient history = (.ok ((value,g),ambient),last)) :
    runPrefix (Admission.actualOps.release peer) w history =
      runPrefix (finish value) {w with wg := g,ambient := ambient}
        (last ++ [receipt peer value w.wg g w.ambient ambient]) := by
  rw [actual_run,performed]

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.PeerRelease
