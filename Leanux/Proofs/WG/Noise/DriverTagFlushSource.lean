import Leanux.Proofs.WG.Noise.DriverTagFlushFactors
import Leanux.Proofs.WG.Noise.DriverTagFlushFrames

/-! Exact original flush sources with explicit callbacks and their composition laws. -/
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.DriverTags.Flush
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
universe u

/-! Generic source erasure and journal-preservation composition. -/

theorem sendWith_erases {E : Type} (worker : PeerId → WGPrefix E Unit)
    (original : PeerId → WG.M Unit) (same : ∀ pid, ErasesStatePrefix (worker pid) (original pid))
    (pid : PeerId) :
    ErasesStatePrefix (sendWith (fun {_} a => liftWGPrefix a) worker pid)
      (sendWith (fun {_} a => a) original pid) := by
  unfold sendWith
  exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
    erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
    erasesStatePrefix_bind (same pid) (fun _ =>
    erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_pure _))))

theorem clearWith_erases {E : Type} (worker : PeerId → WGPrefix E Unit)
    (original : PeerId → WG.M Unit) (same : ∀ pid, ErasesStatePrefix (worker pid) (original pid))
    (pid : PeerId) :
    ErasesStatePrefix (clearWith (fun {_} a => liftWGPrefix a) worker pid)
      (clearWith (fun {_} a => a) original pid) := by
  unfold clearWith
  exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
    erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
    erasesStatePrefix_bind (same pid) (fun _ =>
    erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => erasesStatePrefix_pure _))))


theorem placeholderWith_erases {E : Type} (send clear : PeerId → WGPrefix E Unit)
    (sendNative clearNative : PeerId → WG.M Unit)
    (hs : ∀ pid, ErasesStatePrefix (send pid) (sendNative pid))
    (hc : ∀ pid, ErasesStatePrefix (clear pid) (clearNative pid))
    (d : Device) (upTo : Option PeerId) :
    ErasesStatePrefix (placeholderWith send clear d upTo)
      (placeholderWith sendNative clearNative d upTo) := by
  unfold placeholderWith
  split
  · exact erasesStatePrefix_bind (hs _) (fun _ => erasesStatePrefix_pure _)
  · apply erasesStatePrefix_bind (hc _)
    intro _
    split <;> exact erasesStatePrefix_pure _
  · exact erasesStatePrefix_pure _

theorem turnWith_erases {E : Type} (send clear : PeerId → WGPrefix E Unit)
    (sendNative clearNative : PeerId → WG.M Unit)
    (hs : ∀ pid, ErasesStatePrefix (send pid) (sendNative pid))
    (hc : ∀ pid, ErasesStatePrefix (clear pid) (clearNative pid))
    (upTo : Option PeerId) :
    ErasesStatePrefix (turnWith (fun {_} a => liftWGPrefix a) send clear upTo)
      (turnWith (fun {_} a => a) sendNative clearNative upTo) := by
  unfold turnWith
  dsimp (config := {zeta := false}) only []
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro d
  split
  · exact erasesStatePrefix_pure _
  · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro next
    cases next with
    | some u =>
      exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun pid =>
        erasesStatePrefix_bind (hs pid) (fun _ => erasesStatePrefix_pure _))
    | none =>
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro next
      cases next with
      | some u =>
        apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
        intro pid
        apply erasesStatePrefix_bind (hc pid)
        intro _
        split <;> exact erasesStatePrefix_pure _
      | none =>
        apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
        intro ambient
        split
        · exact erasesStatePrefix_bind (erasesStatePrefix_lift _)
            (fun _ => placeholderWith_erases send clear sendNative clearNative hs hc d upTo)
        · exact placeholderWith_erases send clear sendNative clearNative hs hc d upTo

theorem drainWith_erases {E : Type} (send clear : PeerId → WGPrefix E Unit)
    (sendNative clearNative : PeerId → WG.M Unit)
    (hs : ∀ pid, ErasesStatePrefix (send pid) (sendNative pid))
    (hc : ∀ pid, ErasesStatePrefix (clear pid) (clearNative pid))
    (upTo : Option PeerId) :
    ErasesStatePrefix (drainWith (fun {_} a => liftWGPrefix a) send clear upTo)
      (drainWith (fun {_} a => a) sendNative clearNative upTo) := by
  unfold drainWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply erasesStatePrefix_bind
  · exact erasesStatePrefix_forIn _ _ _ _ (fun _ _ =>
      turnWith_erases send clear sendNative clearNative hs hc upTo)
  · rintro ⟨returned,_⟩
    cases returned <;> first | exact erasesStatePrefix_lift _ | exact erasesStatePrefix_pure _

theorem timersWith_erases {E : Type}
    (deleted : PeerId → PeerTimer → WGPrefix E Unit) (drain : Option PeerId → WGPrefix E Unit)
    (deletedNative : PeerId → PeerTimer → WG.M Unit) (drainNative : Option PeerId → WG.M Unit)
    (hd : ∀ pid timer, ErasesStatePrefix (deleted pid timer) (deletedNative pid timer))
    (hf : ∀ target, ErasesStatePrefix (drain target) (drainNative target))
    (pid : PeerId) :
    ErasesStatePrefix (timersWith (fun {_} a => liftWGPrefix a) deleted drain pid)
      (timersWith (fun {_} a => a) deletedNative drainNative pid) := by
  unfold timersWith
  apply erasesStatePrefix_bind
  · apply erasesStatePrefix_forIn
    intro timer state
    exact erasesStatePrefix_bind (hd pid timer) (fun _ => erasesStatePrefix_pure _)
  · intro _
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro d
    split
    · exact hf _
    · exact erasesStatePrefix_pure _

theorem list_preserves {E α β : Type} (I : List E → WGWorld → Ambient → Prop)
    (S : List E → Prop) (safe : ∀ h g ambient, I h g ambient → S h)
    (xs : List α) (init : β) (body : α → β → WGPrefix E (ForInStep β))
    (step : ∀ a b, StatePrefixPreserves I S (body a b)) :
    StatePrefixPreserves I S (forIn xs init body) :=
  StatePrefixEnsures.forInInvariant xs init body (fun _ => I) S (fun _ => safe) step

theorem sendWith_preserves {E : Type} (I : List E → WGWorld → Ambient → Prop)
    (S : List E → Prop) (safe : ∀ h g ambient, I h g ambient → S h)
    (worker : PeerId → WGPrefix E Unit)
    (prepare : ∀ pid, StatePrefixPreserves I S (liftWGPrefix (Index.flushedSendPrepare pid)))
    (ambient : ∀ {α : Type} (a : AmbientM α), StatePrefixPreserves I S
      (liftWGPrefix (StateT.lift a : WG.M α)))
    (hw : ∀ pid, StatePrefixPreserves I S (worker pid)) (pid : PeerId) :
    StatePrefixPreserves I S (sendWith (fun {_} a => liftWGPrefix a) worker pid) := by
  unfold sendWith
  exact StatePrefixEnsures.bind (prepare pid) (fun _ =>
    StatePrefixEnsures.bind (ambient _) (fun _ =>
    StatePrefixEnsures.bind (hw pid) (fun _ =>
    StatePrefixEnsures.bind (ambient _) (fun _ =>
      StatePrefixEnsures.pure () safe (fun _ _ _ hi => hi)))))

theorem clearWith_preserves {E : Type} (I : List E → WGWorld → Ambient → Prop)
    (S : List E → Prop) (safe : ∀ h g ambient, I h g ambient → S h)
    (worker : PeerId → WGPrefix E Unit)
    (dequeue : ∀ pid, StatePrefixPreserves I S
      (liftWGPrefix (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})))
    (ambient : ∀ {α : Type} (a : AmbientM α), StatePrefixPreserves I S
      (liftWGPrefix (StateT.lift a : WG.M α)))
    (hw : ∀ pid, StatePrefixPreserves I S (worker pid)) (pid : PeerId) :
    StatePrefixPreserves I S (clearWith (fun {_} a => liftWGPrefix a) worker pid) := by
  unfold clearWith
  exact StatePrefixEnsures.bind (dequeue pid) (fun _ =>
    StatePrefixEnsures.bind (ambient _) (fun _ =>
    StatePrefixEnsures.bind (hw pid) (fun _ =>
    StatePrefixEnsures.bind (ambient _) (fun _ =>
      StatePrefixEnsures.pure () safe (fun _ _ _ hi => hi)))))


theorem placeholderWith_preserves {E : Type} (I : List E → WGWorld → Ambient → Prop)
    (S : List E → Prop) (safe : ∀ h g ambient, I h g ambient → S h)
    (send clear : PeerId → WGPrefix E Unit)
    (hs : ∀ pid, StatePrefixPreserves I S (send pid))
    (hc : ∀ pid, StatePrefixPreserves I S (clear pid)) (d : Device) (upTo : Option PeerId) :
    StatePrefixPreserves I S (placeholderWith send clear d upTo) := by
  have pureValue {α : Type} (x : α) : StatePrefixPreserves I S (pure x : WGPrefix E α) :=
    StatePrefixEnsures.pure x safe (fun _ _ _ hi => hi)
  unfold placeholderWith
  split
  · exact StatePrefixEnsures.bind (hs _) (fun _ => pureValue _)
  · apply StatePrefixEnsures.bind (hc _)
    intro _
    split <;> exact pureValue _
  · exact pureValue _

theorem turnWith_preserves {E : Type} (I : List E → WGWorld → Ambient → Prop)
    (S : List E → Prop) (safe : ∀ h g ambient, I h g ambient → S h)
    (send clear : PeerId → WGPrefix E Unit)
    (ambient : ∀ {α : Type} (a : AmbientM α), StatePrefixPreserves I S
      (liftWGPrefix (StateT.lift a : WG.M α)))
    (dev : StatePrefixPreserves I S (liftWGPrefix getDev))
    (hs : ∀ pid, StatePrefixPreserves I S (send pid))
    (hc : ∀ pid, StatePrefixPreserves I S (clear pid)) (upTo : Option PeerId) :
    StatePrefixPreserves I S (turnWith (fun {_} a => liftWGPrefix a) send clear upTo) := by
  have pureValue {α : Type} (x : α) : StatePrefixPreserves I S (pure x : WGPrefix E α) :=
    StatePrefixEnsures.pure x safe (fun _ _ _ hi => hi)
  have fallback (d : Device) := placeholderWith_preserves I S safe send clear hs hc d upTo
  have stop {α : Type} (reason : Stop) :
      StatePrefixPreserves I S (liftWGPrefix (throw reason : WG.M α)) := by
    apply StatePrefixEnsures.lift
    · exact safe
    · intro g w a result final after hi run
      cases run
  unfold turnWith
  refine StatePrefixEnsures.bind dev ?_
  intro d
  split
  · exact pureValue _
  · refine StatePrefixEnsures.bind (ambient (AmbientM.peekUnit .sendWorker)) ?_
    intro next
    cases next with
    | some u =>
      exact StatePrefixEnsures.bind (ambient (AmbientM.resolveUnit .sendWorker u _)) (fun pid =>
        StatePrefixEnsures.bind (hs pid) (fun _ => pureValue _))
    | none =>
      refine StatePrefixEnsures.bind (ambient (AmbientM.peekUnit .clearPeerWorker)) ?_
      intro next
      cases next with
      | some u =>
        refine StatePrefixEnsures.bind (ambient (AmbientM.resolveUnit .clearPeerWorker u _)) ?_
        intro pid
        refine StatePrefixEnsures.bind (hc pid) ?_
        intro _
        split <;> exact pureValue _
      | none =>
        refine StatePrefixEnsures.bind (ambient (get : AmbientM Ambient)) ?_
        intro inputs
        split
        · exact StatePrefixEnsures.bind (stop _) (fun _ => fallback d)
        · exact fallback d

theorem drainWith_preserves {E : Type} (I : List E → WGWorld → Ambient → Prop)
    (S : List E → Prop) (safe : ∀ h g ambient, I h g ambient → S h)
    (send clear : PeerId → WGPrefix E Unit)
    (ambient : ∀ {α : Type} (a : AmbientM α), StatePrefixPreserves I S
      (liftWGPrefix (StateT.lift a : WG.M α)))
    (dev : StatePrefixPreserves I S (liftWGPrefix getDev))
    (hs : ∀ pid, StatePrefixPreserves I S (send pid))
    (hc : ∀ pid, StatePrefixPreserves I S (clear pid)) (upTo : Option PeerId) :
    StatePrefixPreserves I S (drainWith (fun {_} a => liftWGPrefix a) send clear upTo) := by
  unfold drainWith
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine StatePrefixEnsures.bind (Q := fun _ => I)
    (list_preserves I S safe _ _ _ (fun _ _ =>
      turnWith_preserves I S safe send clear ambient dev hs hc upTo)) ?_
  rintro ⟨returned,_⟩
  cases returned with
  | none => exact ambient (AmbientM.invariant _)
  | some value => exact StatePrefixEnsures.pure value safe (fun _ _ _ hi => hi)

theorem timersWith_preserves {E : Type} (I : List E → WGWorld → Ambient → Prop)
    (S : List E → Prop) (safe : ∀ h g ambient, I h g ambient → S h)
    (deleted : PeerId → PeerTimer → WGPrefix E Unit) (drain : Option PeerId → WGPrefix E Unit)
    (dev : StatePrefixPreserves I S (liftWGPrefix getDev))
    (hd : ∀ pid timer, StatePrefixPreserves I S (deleted pid timer))
    (hf : ∀ target, StatePrefixPreserves I S (drain target)) (pid : PeerId) :
    StatePrefixPreserves I S (timersWith (fun {_} a => liftWGPrefix a) deleted drain pid) := by
  have pureValue {α : Type} (x : α) : StatePrefixPreserves I S (pure x : WGPrefix E α) :=
    StatePrefixEnsures.pure x safe (fun _ _ _ hi => hi)
  unfold timersWith
  refine StatePrefixEnsures.bind (Q := fun _ => I) (list_preserves I S safe _ _ _ ?_) ?_
  · intro timer state
    exact StatePrefixEnsures.bind (hd pid timer) (fun _ => pureValue _)
  · intro _
    exact StatePrefixEnsures.bind dev (fun d => by split; exact hf _; exact pureValue _)


end Leanux.Proofs.WG.Noise.DriverTags.Flush
