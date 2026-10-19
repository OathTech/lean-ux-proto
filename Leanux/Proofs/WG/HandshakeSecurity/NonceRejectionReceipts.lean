import Leanux.Proofs.WG.HandshakeSecurity.NonceRejectionFrames

/-! The rejection observer executes each original write once. A stopped
continuation retains every completed invalidation/restoration receipt. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.NonceRejection
open Leanux Leanux.WG Leanux.Proofs.Logged

def Sound (h : List Event) : Prop := ∀ e ∈ h, e.Valid

private theorem sound_append (old : Sound h) (valid : e.Valid) : Sound (h ++ [e]) := by
  intro event member
  rcases List.mem_append.mp member with before | fresh
  · exact old event before
  · have same := List.mem_singleton.mp fresh
    exact same ▸ valid

private theorem receipt (action : WG.M Unit) (make : WGRunWitness Unit → Event)
    (valid : ∀ r, r.Valid action → (make r).Valid) :
    StatePrefixEnsures (fun h _ _ => Sound h) Sound (receiptWGObserved (liftWGPrefix action) make)
      (fun _ h _ _ => Sound h) := by
  unfold receiptWGObserved
  change StatePrefixEnsures _ _ (do
    let r ← captureWGRun action
    emitStatePrefix (make r)
    pure r.value) _
  have captured : StatePrefixEnsures (fun h _ _ => Sound h) Sound (captureWGRun action)
      (fun r h _ _ => Sound h ∧ (make r).Valid) := by
    apply StatePrefixEnsures.captureWGRun (P := fun h _ _ => Sound h) (S := Sound) action (fun _ _ _ hi => hi)
    intro h w a x v b hi run
    exact ⟨hi,valid ⟨x,w,v,a,b⟩ run⟩
  apply StatePrefixEnsures.bind captured
  intro r
  apply StatePrefixEnsures.bind (Q := fun _ h _ _ => Sound h)
  · exact StatePrefixEnsures.emit _ (fun _ _ _ hi => sound_append hi.1 hi.2)
      (fun _ _ _ hi => sound_append hi.1 hi.2)
  · intro _
    exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi) (fun _ _ _ hi => hi)

private theorem lift (action : WG.M α) :
    StatePrefixEnsures (fun h _ _ => Sound h) Sound (liftWGPrefix action) (fun _ h _ _ => Sound h) :=
  StatePrefixEnsures.lift action (fun _ _ _ hi => hi) (fun _ _ _ _ _ _ hi _ => hi)

theorem sound (pid : PeerId) (packets : List Packet) (kid : KeypairId) :
    StatePrefixPreserves (fun h _ _ => Sound h) Sound (observe pid packets kid) := by
  unfold observe
  apply StatePrefixEnsures.bind (receipt (invalidate kid) (.invalidated kid) (fun _ valid => valid))
  intro _
  apply StatePrefixEnsures.bind (lift _)
  intro _
  apply StatePrefixEnsures.bind (receipt (restore pid packets) (.restored pid packets) (fun _ valid => valid))
  intro _
  exact lift _

/-- Emitted effects before Stop are actual original writes, not inferred from
a normally completed send or handshake request. -/
theorem actual_receipts (pid : PeerId) (packets : List Packet) (kid : KeypairId)
    (w : WGWorld) (a : Ambient) :
    Sound (runWGPrefix (observe pid packets kid) w a []).2 := by
  obtain ⟨_,_,safe,_⟩ := sound pid packets kid w a [] (by intro e member; cases member)
  exact safe

theorem observe_run (pid : PeerId) (packets : List Packet) (kid : KeypairId)
    (w : WGWorld) (a : Ambient) (h : List Event) :
    runWGPrefix (observe pid packets kid) w a h =
      match ((invalidate kid).run w).run a with
      | .error stop => (.error stop,h)
      | .ok (((),u),b) =>
        let first : Event := .invalidated kid ⟨(),w,u,a,b⟩
        match ((release kid packets).run u).run b with
        | .error stop => (.error stop,h ++ [first])
        | .ok (((),v),c) =>
          match ((restore pid packets).run v).run c with
          | .error stop => (.error stop,h ++ [first])
          | .ok (((),z),d) =>
            (((sendQueuedHandshakeInitiation pid false).run z).run d,
              (h ++ [first]) ++ [.restored pid packets ⟨(),v,z,c,d⟩]) := by
  unfold observe
  change runStatePrefix _ w a h = _
  rw [runStatePrefix_bind]
  have first := runWGPrefix_receiptWGObserved (liftWGPrefix (invalidate kid)) (Event.invalidated kid) w a h
  rw [runWGPrefix_lift] at first
  change runStatePrefix _ w a h = _ at first
  rw [first]
  cases invalidated : ((invalidate kid).run w).run a with
  | error stop => rfl
  | ok out =>
    obtain ⟨⟨returned,u⟩,b⟩ := out
    cases returned
    simp only
    rw [runStatePrefix_bind,liftWGPrefix,runStatePrefix_lift]
    cases released : ((release kid packets).run u).run b with
    | error stop => rfl
    | ok out =>
      obtain ⟨⟨returned,v⟩,c⟩ := out
      cases returned
      simp only
      rw [runStatePrefix_bind]
      have restored := runWGPrefix_receiptWGObserved (liftWGPrefix (restore pid packets))
        (Event.restored pid packets) v c (h ++ [.invalidated kid ⟨(),w,u,a,b⟩])
      rw [runWGPrefix_lift] at restored
      change runStatePrefix _ v c _ = _ at restored
      rw [restored]
      cases restoration : ((restore pid packets).run v).run c with
      | error stop => rfl
      | ok out =>
        obtain ⟨⟨returned,z⟩,d⟩ := out
        cases returned
        rfl

/-- Every normally completed rejection contains both ordered native writes.
The queue-helper call begins only after restoration has committed. -/
theorem normal_receipts (pid : PeerId) (packets : List Packet) (kid : KeypairId)
    (w v : WGWorld) (a b : Ambient)
    (run : ((Lifetimes.stagedOutNokey pid packets (some kid) true).run w).run a = .ok (((),v),b)) :
    ∃ first second : WGRunWitness Unit,
      first.before = w ∧ first.ambientBefore = a ∧ first.Valid (invalidate kid) ∧
      ((release kid packets).run first.after).run first.ambientAfter =
        .ok (((),second.before),second.ambientBefore) ∧
      second.Valid (restore pid packets) ∧
      ((sendQueuedHandshakeInitiation pid false).run second.after).run second.ambientAfter = .ok (((),v),b) ∧
      (runWGPrefix (observe pid packets kid) w a []).2 = [.invalidated kid first,.restored pid packets second] := by
  have source := (erases pid packets kid w a []).trans run
  change (runWGPrefix (observe pid packets kid) w a []).1 = .ok (((),v),b) at source
  rw [observe_run] at source ⊢
  cases invalidated : ((invalidate kid).run w).run a with
  | error stop => simp [invalidated] at source
  | ok out =>
    obtain ⟨⟨returned,u⟩,c⟩ := out
    cases returned
    simp only [invalidated] at source ⊢
    cases released : ((release kid packets).run u).run c with
    | error stop => simp [released] at source
    | ok out =>
      obtain ⟨⟨returned,z⟩,d⟩ := out
      cases returned
      simp only [released] at source ⊢
      cases restored : ((restore pid packets).run z).run d with
      | error stop => simp [restored] at source
      | ok out =>
        obtain ⟨⟨returned,t⟩,e⟩ := out
        cases returned
        simp only [restored] at source ⊢
        exact ⟨⟨(),w,u,a,c⟩,⟨(),z,t,d,e⟩,rfl,rfl,invalidated,released,restored,source,rfl⟩

end Leanux.Proofs.WG.HandshakeSecurity.NonceRejection
