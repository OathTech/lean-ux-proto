import Leanux.Proofs.WG.Index.FlushFrames
import Leanux.Proofs.WG.Index.ClearSource
import Leanux.Proofs.WG.Index.TimerFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem runFlushedSendWork_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ runFlushedSendWork pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have pureValue {α : Type} (value : α) :
      Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have dev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g inputs result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have peer : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g inputs result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g inputs result final after pre run).1
  have tail (p : Peer) : Ensures (do
      let d ← getDev
      setPeer pid {p with handshakePending := d.sendWorkQueue.contains pid}
      let _ ← hidden (.sectionStart .sendWorker)
      handshakeSendWorker pid
      let _ ← hidden (.sectionStop .sendWorker)
      pure ()) TablesSafeWG (fun _ => TablesSafeWG) := by
    refine ensures_bind _ _ dev ?_
    intro d
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (setPeer_tables pid _)) ?_
    intro _
    refine ensures_bind _ _ (ambient (AmbientM.hidden (.sectionStart .sendWorker))) ?_
    intro _
    refine ensures_bind _ _ (handshakeSendWorker_tables pid) ?_
    intro _
    refine ensures_bind _ _ (ambient (AmbientM.hidden (.sectionStop .sendWorker))) ?_
    intro _
    exact pureValue ()
  apply (ensures_iff _ _ _).mp
  unfold runFlushedSendWork
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (modifySendWorkQueue_tables (fun queue => queue.erase pid))) ?_
  intro _
  refine ensures_bind _ _ peer ?_
  intro p
  split
  · exact ensures_bind _ _ (ambient (AmbientM.invariant "queued work without a pending flag"))
      (fun _ => tail p)
  · exact tail p

theorem runFlushedClearWork_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ runFlushedClearWork pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  apply (ensures_iff _ _ _).mp
  unfold runFlushedClearWork
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (modifyClearWorkQueue_tables (fun queue => queue.erase pid))) ?_
  intro _
  refine ensures_bind _ _ (ambient (AmbientM.hidden (.sectionStart .clearPeerWorker))) ?_
  intro _
  refine ensures_bind _ _ (queuedExpiredZeroKeyMaterial_tables pid) ?_
  intro _
  refine ensures_bind _ _ (ambient (AmbientM.hidden (.sectionStop .clearPeerWorker))) ?_
  intro _ g inputs result final after pre run
  cases run
  exact pre

/-- The original bounded drain, including named selection, placeholder order,
early return at the requested clear work, and its original stopped outcomes. -/
theorem drainHandshakeSendWq_tables (upTo : Option PeerId) :
    Ensures (drainHandshakeSendWq upTo) TablesSafeWG (fun _ => TablesSafeWG) := by
  have pureValue {α : Type} (value : α) :
      Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have dev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g inputs result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have listFrame {α β : Type} (xs : List α) (initial : β)
      (body : α → β → WG.M (ForInStep β))
      (step : ∀ a b, Ensures (body a b) TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (forIn xs initial body) TablesSafeWG (fun _ => TablesSafeWG) := by
    induction xs generalizing initial with
    | nil => simpa only [List.forIn_nil] using pureValue initial
    | cons x xs ih =>
      rw [List.forIn_cons]
      refine ensures_bind _ _ (step x initial) ?_
      intro result
      cases result with
      | done final => exact pureValue final
      | yield next => exact ih next
  have send (pid : PeerId) := (ensures_iff _ _ _).mpr (runFlushedSendWork_tables pid)
  have clear (pid : PeerId) := (ensures_iff _ _ _).mpr (runFlushedClearWork_tables pid)
  have peek (worker : Worker) : Ensures (peekUnit worker : WG.M (Option Nat))
      TablesSafeWG (fun _ => TablesSafeWG) := ambient (AmbientM.peekUnit worker)
  have resolve (worker : Worker) (unit : Nat) (queue : List Nat) :
      Ensures (resolveUnit worker unit queue : WG.M Nat) TablesSafeWG (fun _ => TablesSafeWG) :=
    ambient (AmbientM.resolveUnit worker unit queue)
  have inputs : Ensures (getAmbient : WG.M Ambient) TablesSafeWG (fun _ => TablesSafeWG) :=
    ambient (get : AmbientM Ambient)
  have stop {α : Type} (reason : Stop) :
      Ensures (throw reason : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a result final after pre run
    cases run
  have inv {α : Type} (what : String) :
      Ensures (invariant what : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    ambient (AmbientM.invariant what)
  unfold drainHandshakeSendWq
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (listFrame _ _ _ ?_) ?_
  · intro turn state
    repeat' first
      | exact pureValue _
      | exact dev
      | exact peek _
      | exact resolve _ _ _
      | exact inputs
      | exact send _
      | exact clear _
      | exact stop _
      | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
      | split
  · rintro ⟨returned, _⟩
    cases returned with
    | none => exact inv _
    | some value => exact pureValue value

/-- Timer deletion and the actual conditional clear-work flush. -/
theorem timersStop_tables (pid : PeerId) :
    Ensures (timersStop pid) TablesSafeWG (fun _ => TablesSafeWG) := by
  have pureValue {α : Type} (value : α) :
      Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have dev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g inputs result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have deleted (timer : PeerTimer) := (ensures_iff _ _ _).mpr (delTimer_tables pid timer)
  unfold timersStop
  simp only [PeerTimer.all, List.forIn_cons, List.forIn_nil, bind_assoc, pure_bind]
  repeat' first
    | exact pureValue _
    | exact dev
    | exact deleted _
    | exact drainHandshakeSendWq_tables _
    | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | split

/-- Actual ordered key releases, both flushes, accounting and final peer release.
The deadness guard remains operational; this contract does not assume it succeeds. -/
theorem peerRemoveAfterDead_tables (pid : PeerId) :
    Ensures (peerRemoveAfterDead pid) TablesSafeWG (fun _ => TablesSafeWG) := by
  have pureValue {α : Type} (value : α) :
      Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have dev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g inputs result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have peer : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g inputs result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g inputs result final after pre run).1
  have branch (site : Decision) (value : Bool) : Ensures (Leanux.branch site value : WG.M Bool)
      TablesSafeWG (fun _ => TablesSafeWG) := ambient (AmbientM.branch site value)
  have inv {α : Type} (what : String) : Ensures (invariant what : WG.M α)
      TablesSafeWG (fun _ => TablesSafeWG) := ambient (AmbientM.invariant what)
  have unsupportedStep {α : Type} (what : String) : Ensures (unsupported what : WG.M α)
      TablesSafeWG (fun _ => TablesSafeWG) := ambient (AmbientM.unsupported what)
  have keys := (ensures_iff _ _ _).mpr (keypairsClear_tables pid)
  have decrement := (ensures_iff _ _ _).mpr decrementNumPeers_tables
  have release := (ensures_iff _ _ _).mpr (peerPut_tables (some pid))
  unfold peerRemoveAfterDead
  repeat' first
    | exact pureValue _
    | exact dev
    | exact peer
    | exact branch _ _
    | exact inv _
    | exact unsupportedStep _
    | exact keys
    | exact timersStop_tables _
    | exact drainHandshakeSendWq_tables _
    | exact decrement
    | exact release
    | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | split

end Leanux.Proofs.WG.Index
