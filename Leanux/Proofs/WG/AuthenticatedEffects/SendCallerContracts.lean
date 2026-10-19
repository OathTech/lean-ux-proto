import Leanux.Proofs.WG.AuthenticatedEffects.DelayedEffectCarrier
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeSource

/-! Real send selectors discharge the live-membership premise. Arbitrary
flushed-worker calls are not granted a queue occurrence by these contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.SendCallers
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open HandshakeSecurity.SendExchange Lifetimes
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

abbrev StateSafe (P : List E → WGWorld → Prop) (S : List E → Prop) (g : WGPrefix E α) :=
  StatePrefixPreserves (fun h w _ => P h w) S g

abbrev SelectedSafe (P : List E → WGWorld → Prop) (S : List E → Prop)
    (pid : PeerId) (g : WGPrefix E α) :=
  StatePrefixEnsures (fun h w _ => P h w ∧ pid ∈ QueuedOccurrences.queue w) S g
    (fun _ h w _ => P h w)

theorem one_preserves (P : List E → WGWorld → Prop) (S : List E → Prop)
    (safe : ∀ h w, P h w → S h) (flushed : PeerId → WGPrefix E Unit)
    (calls : ∀ pid, SelectedSafe P S pid (flushed pid)) :
    PrefixPreserves (fun h w => P h w.wg) S
      (oneWith liftPrefix (fun pid => liftWGObserver (flushed pid))) := by
  apply PrefixEnsures.preserves
  unfold oneWith
  apply PrefixEnsures.bind (Q := fun pid h w => P h w.wg ∧ pid ∈ QueuedOccurrences.queue w.wg)
  · apply PrefixEnsures.lift _ (fun h w hi => safe h w.wg hi)
    intro h w pid v hi run
    obtain ⟨same,member⟩ := SendWorkCauses.select_member w v pid run
    exact ⟨same ▸ hi,by simpa only [same,SendWorkCauses.queue,QueuedOccurrences.queue] using member⟩
  · intro pid
    exact (calls pid).liftWGObserver

private theorem ambient_frame (action : AmbientM α) (P : List E → WGWorld → Prop)
    (S : List E → Prop) (safe : ∀ h w, P h w → S h) :
    StateSafe P S (liftWGPrefix (MonadLift.monadLift action : WG.M α)) := by
  apply StatePrefixEnsures.lift _ (fun h w _ hi => safe h w hi)
  intro h w a value v b hi run
  have same := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient action (fun world => world = w)) w a value v b rfl run
  exact same ▸ hi

private theorem getDev_checked (P : List E → WGWorld → Prop) (S : List E → Prop)
    (safe : ∀ h w, P h w → S h) :
    StatePrefixEnsures (fun h w _ => P h w) S (liftWGPrefix getDev)
      (fun d h w _ => P h w ∧ w.dev = some d) := by
  apply StatePrefixEnsures.lift _ (fun h w _ hi => safe h w hi)
  intro h w a d v b hi run
  obtain ⟨rfl,rfl,device⟩ := Queues.RxCredits.DecryptCarrier.getDev_current a b run
  exact ⟨hi,device⟩

private theorem resolve_checked (P : List E → WGWorld → Prop) (S : List E → Prop)
    (safe : ∀ h w, P h w → S h) (worker : Worker) (unit : Nat) (queue : List Nat) :
    StatePrefixEnsures (fun h w _ => P h w) S (liftWGPrefix (resolveUnit worker unit queue))
      (fun pid h w _ => P h w ∧ pid ∈ queue) := by
  apply StatePrefixEnsures.lift _ (fun h w _ hi => safe h w hi)
  intro h w a pid v b hi run
  change (((StateT.lift (AmbientM.resolveUnit worker unit queue) : WG.M Nat).run w).run a) = _ at run
  rw [stateLiftAmbient_run] at run
  cases native : (AmbientM.resolveUnit worker unit queue).run a with
  | error stop => simp [native,Except.map] at run
  | ok result =>
    rcases result with ⟨selected,after⟩
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact ⟨hi,(Queues.RxCredits.ClearWork.resolveUnit_member worker unit queue a after selected native).1⟩


/-- The native finite drain checks actual queue membership before each send,
including recorded-unit dispatch and the unrecorded head fallback. -/
theorem drain_preserves (P : List E → WGWorld → Prop) (S : List E → Prop)
    (safe : ∀ h w, P h w → S h) (send clear : PeerId → WGPrefix E Unit)
    (sends : ∀ pid, SelectedSafe P S pid (send pid))
    (clears : ∀ pid, StateSafe P S (clear pid)) (upTo : Option PeerId) :
    StateSafe P S (drainWith liftWGPrefix send clear upTo) := by
  unfold drainWith
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply StatePrefixEnsures.bind
  · apply StatePrefixEnsures.forInInvariant _ _ _ (fun _ h w _ => P h w) S
    · intro value h w a hi
      exact safe h w hi
    · intro i acc
      apply StatePrefixEnsures.bind (getDev_checked P S safe)
      intro d
      dsimp only
      split
      · exact StatePrefixEnsures.pure _ (fun h w _ hi => safe h w hi.1) (fun _ _ _ hi => hi.1)
      · apply StatePrefixEnsures.bind (ambient_frame (AmbientM.peekUnit .sendWorker)
          (fun h w => P h w ∧ w.dev = some d) S (fun h w hi => safe h w hi.1))
        intro unit
        cases unit with
        | some u =>
          apply StatePrefixEnsures.bind (resolve_checked (fun h w => P h w ∧ w.dev = some d)
            S (fun h w hi => safe h w hi.1) .sendWorker u d.sendWorkQueue)
          intro pid
          apply StatePrefixEnsures.bind
          · exact (sends pid).consequence
              (fun h w _ hi => ⟨hi.1.1,by simpa only [QueuedOccurrences.queue,hi.1.2,
                Option.map_some,Option.getD_some] using hi.2⟩)
              (fun _ _ _ _ hi => hi)
          · intro value
            exact StatePrefixEnsures.pure _ (fun h w _ hi => safe h w hi) (fun _ _ _ hi => hi)
        | none =>
          apply StatePrefixEnsures.bind (ambient_frame (AmbientM.peekUnit .clearPeerWorker)
            (fun h w => P h w ∧ w.dev = some d) S (fun h w hi => safe h w hi.1))
          intro unit
          cases unit with
          | some u =>
            apply StatePrefixEnsures.bind (resolve_checked (fun h w => P h w ∧ w.dev = some d)
              S (fun h w hi => safe h w hi.1) .clearPeerWorker u d.clearWorkQueue)
            intro pid
            apply StatePrefixEnsures.bind
            · exact (clears pid).consequence (fun _ _ _ hi => hi.1.1) (fun _ _ _ _ hi => hi)
            · intro value
              split <;> exact StatePrefixEnsures.pure _ (fun h w _ hi => safe h w hi) (fun _ _ _ hi => hi)
          | none =>
            apply StatePrefixEnsures.bind (ambient_frame (get : AmbientM Ambient)
              (fun h w => P h w ∧ w.dev = some d) S (fun h w hi => safe h w hi.1))
            intro ambient
            split
            · exact (ambient_frame (throw _ : AmbientM _) P S safe).consequence
                (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)
            · cases hs : d.sendWorkQueue.head? with
              | some pid =>
                apply StatePrefixEnsures.bind
                · exact (sends pid).consequence
                    (fun h w _ hi => ⟨hi.1,by simpa only [QueuedOccurrences.queue,hi.2,
                      Option.map_some,Option.getD_some] using List.mem_of_head? hs⟩)
                    (fun _ _ _ _ hi => hi)
                · intro value
                  exact StatePrefixEnsures.pure _ (fun h w _ hi => safe h w hi) (fun _ _ _ hi => hi)
              | none =>
                cases hc : d.clearWorkQueue.head? with
                | none =>
                  exact StatePrefixEnsures.pure _ (fun h w _ hi => safe h w hi.1) (fun _ _ _ hi => hi.1)
                | some pid =>
                  apply StatePrefixEnsures.bind
                  · exact (clears pid).consequence (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)
                  · intro value
                    split <;> exact StatePrefixEnsures.pure _ (fun h w _ hi => safe h w hi) (fun _ _ _ hi => hi)
  · intro result
    rcases result with ⟨result,⟨⟩⟩
    cases result with
    | none => exact ambient_frame (AmbientM.invariant _) P S safe
    | some result => exact StatePrefixEnsures.pure result (fun h w _ hi => safe h w hi) (fun _ _ _ hi => hi)

end Leanux.Proofs.WG.AuthenticatedEffects.SendCallers
