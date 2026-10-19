import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalPeerProjection
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDecoration

/-! A successful counted peer-release cut is recorded before its potentially
stopped suffix. The old peer-access callbacks execute on that same history. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.PeerSource
open Leanux Leanux.WG Leanux.Proofs.Logged

def observed (o : Ops (WGPrefix E)) (record : Event → E) (peer : Option PeerId) :
    WGPrefix E Unit := do
  match ← receiptWGObserved (cutWith o peer) (fun r => record (.release peer r)) with
  | none => pure ()
  | some (pid,p) => o.step (releaseFinish pid p)

theorem observed_erases {o : Ops (WGPrefix E)} (h : Ops.Erases o)
    (record : Event → E) (peer : Option PeerId) :
    ErasesStatePrefix (observed o record peer) (peerPut peer) := by
  rw [release_factor]
  unfold observed
  apply erasesStatePrefix_bind (receiptWGObserved_erases (cut_erases h peer) _)
  intro result
  cases result with
  | none => exact erasesStatePrefix_pure _
  | some out => exact h.step _

theorem observed_projects {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}
    (ρ : E → Option F) (h : Ops.Projects ρ g t)
    (record : Event → E) (quiet : ∀ event, ρ (record event) = none)
    (peer : Option PeerId) :
    StateProjectsPrefix ρ id (observed g record peer) (putWith t peer) := by
  unfold observed putWith
  repeat' first
    | exact Exchange.receipt_ignored ρ _ _ _ (cut_projects ρ h peer) (fun _ => quiet _)
    | disposal_peer_project h ρ

/-- The original lifetime observer is recovered with all its events intact,
including a counted release followed by a stopped timer check. -/
theorem observed_peers_projects {g : Ops (WGPrefix E)} (ρ : E → Option Peers.PeerEvent)
    (h : Ops.Projects ρ g peers) (record : Event → E)
    (quiet : ∀ event, ρ (record event) = none) (peer : Option PeerId) :
    StateProjectsPrefix ρ id (observed g record peer) (Peers.peerPutPrefix peer) := by
  rw [← put_peers]
  exact observed_projects ρ h record quiet peer

/-- This is the actual cut's entry and outcome, before any suffix call. -/
theorem cut_receipt_valid {g : Ops (WGPrefix E)} (h : Ops.Erases g)
    (peer : Option PeerId) (w v : WGWorld) (a b : Ambient) (history tail : List E)
    (value : Option (PeerId × Peer))
    (run : runWGPrefix (cutWith g peer) w a history = (.ok ((value,v),b),tail)) :
    Event.Valid (.release peer ⟨value,w,v,a,b⟩) := by
  have erased := cut_erases h peer w a history
  change (runWGPrefix (cutWith g peer) w a history).1 = _ at erased
  rw [run] at erased
  exact erased.symm

/-- Once the actual counted erase has completed, the receipt is already in
the input history of the native retirement suffix; no normal return is needed. -/
theorem observed_after_cut (g : Ops (WGPrefix E)) (record : Event → E)
    (peer : Option PeerId) (pid : PeerId) (p : Peer)
    (w v : WGWorld) (a b : Ambient) (history tail : List E)
    (run : runWGPrefix (cutWith g peer) w a history = (.ok ((some (pid,p),v),b),tail)) :
    runWGPrefix (observed g record peer) w a history =
      runWGPrefix (g.step (releaseFinish pid p)) v b
        (tail ++ [record (.release peer ⟨some (pid,p),w,v,a,b⟩)]) := by
  unfold observed
  change runStatePrefix _ w a history = _
  rw [runStatePrefix_bind]
  have captured := runWGPrefix_receiptWGObserved (cutWith g peer)
    (fun r => record (.release peer r)) w a history
  rw [run] at captured
  simp only [runWGPrefix] at captured
  rw [captured]
  rfl

theorem observed_retains_release (g : Ops (WGPrefix E)) (record : Event → E)
    (peer : Option PeerId) (pid : PeerId) (p : Peer)
    (appends : StateAppends (g.step (releaseFinish pid p)))
    (w v : WGWorld) (a b : Ambient) (history tail : List E)
    (run : runWGPrefix (cutWith g peer) w a history = (.ok ((some (pid,p),v),b),tail)) :
    ∃ suffix, (runWGPrefix (observed g record peer) w a history).2 =
      tail ++ record (.release peer ⟨some (pid,p),w,v,a,b⟩) :: suffix := by
  rw [observed_after_cut g record peer pid p w v a b history tail run]
  obtain ⟨suffix,eq⟩ := appends v b (tail ++ [record (.release peer ⟨some (pid,p),w,v,a,b⟩)])
  exact ⟨suffix, by simpa only [runWGPrefix,runStatePrefix,List.append_assoc,List.singleton_append] using eq⟩

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.PeerSource
