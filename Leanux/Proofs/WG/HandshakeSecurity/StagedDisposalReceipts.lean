import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalFrames

/-! Receipts occur after actual counted disposal and remain in the history if
a later native suffix stops. These local cuts do not assert global coverage. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem release_run (peer : Option PeerId) (w : WGWorld) (a : Ambient)
    (h : List Event) :
    runWGPrefix (releaseObserved peer) w a h =
      match ((releaseCut peer).run w).run a with
      | .error stop => (.error stop,h)
      | .ok ((result,v),b) =>
        let hist := h ++ [.release peer ⟨result,w,v,a,b⟩]
        match result with
        | none => (.ok (((),v),b),hist)
        | some (pid,p) => (((releaseFinish pid p).run v).run b,hist) := by
  unfold releaseObserved
  change runStatePrefix _ w a h = _
  rw [runStatePrefix_bind]
  have first := runWGPrefix_receiptWGObserved (liftWGPrefix (releaseCut peer))
    (Event.release peer) w a h
  rw [runWGPrefix_lift] at first
  change runStatePrefix _ w a h = _ at first
  rw [first]
  cases executed : ((releaseCut peer).run w).run a with
  | error stop => rfl
  | ok out =>
    obtain ⟨⟨result,v⟩,b⟩ := out
    cases result with
    | none => rfl
    | some pair => rfl

/-- A final release's counted staged purge is retained even when its actual
post-erase timer check or dispatch-retirement suffix stops. -/
theorem release_retained_after_stop (peer : Option PeerId) (pid : PeerId) (p : Peer)
    (r : WGRunWitness (Option (PeerId × Peer)))
    (valid : r.Valid (releaseCut peer)) (selected : r.value = some (pid,p))
    (stop : Stop)
    (later : ((releaseFinish pid p).run r.after).run r.ambientAfter = .error stop)
    (h : List Event) :
    runWGPrefix (releaseObserved peer) r.before r.ambientBefore h =
      (.error stop,h ++ [.release peer r]) := by
  rw [release_run,valid]
  rcases r with ⟨value,w,v,a,b⟩
  dsimp only at selected later ⊢
  subst value
  simp only [later]

theorem release_receipts (peer : Option PeerId) (w : WGWorld) (a : Ambient)
    (h : List Event) (event : Event)
    (member : event ∈ (runWGPrefix (releaseObserved peer) w a h).2) :
    event ∈ h ∨ Event.Valid event := by
  rw [release_run] at member
  cases executed : ((releaseCut peer).run w).run a with
  | error stop => exact Or.inl (by simpa only [executed] using member)
  | ok out =>
    obtain ⟨⟨result,v⟩,b⟩ := out
    have hist : (runWGPrefix (releaseObserved peer) w a h).2 =
        h ++ [.release peer ⟨result,w,v,a,b⟩] := by
      rw [release_run,executed]
      cases result <;> rfl
    have included : event ∈ h ++ [.release peer ⟨result,w,v,a,b⟩] := by
      rw [release_run] at hist
      rw [← hist]
      exact member
    rcases List.mem_append.mp included with previous | current
    · exact Or.inl previous
    · have same := List.mem_singleton.mp current
      subst event
      exact Or.inr executed

theorem purge_receipts (pid : PeerId) (w : WGWorld) (a : Ambient)
    (h : List Event) (event : Event)
    (member : event ∈ (runWGPrefix (purgeObserved pid) w a h).2) :
    event ∈ h ∨ Event.Valid event := by
  unfold purgeObserved at member
  rw [runWGPrefix_receiptWGObserved,runWGPrefix_lift] at member
  cases executed : ((purgeStagedPackets pid).run w).run a with
  | error stop => exact Or.inl (by simpa only [executed] using member)
  | ok out =>
    obtain ⟨⟨result,v⟩,b⟩ := out
    simp only [executed,List.mem_append,List.mem_singleton] at member
    rcases member with previous | rfl
    · exact Or.inl previous
    · exact Or.inr executed

theorem overflow_receipts (pid : PeerId) (w : WGWorld) (a : Ambient)
    (h : List Event) (event : Event)
    (member : event ∈ (runWGPrefix (overflowObserved pid) w a h).2) :
    event ∈ h ∨ Event.Valid event := by
  unfold overflowObserved at member
  rw [runWGPrefix_receiptWGObserved,runWGPrefix_lift] at member
  cases executed : ((Lifetimes.xmitTrim pid).run w).run a with
  | error stop => exact Or.inl (by simpa only [executed] using member)
  | ok out =>
    obtain ⟨⟨result,v⟩,b⟩ := out
    simp only [executed,List.mem_append,List.mem_singleton] at member
    rcases member with previous | rfl
    · exact Or.inl previous
    · exact Or.inr executed

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal
