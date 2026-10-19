import Leanux.Proofs.WG.Index.FlushFactors
import Leanux.Proofs.WG.Index.FlushFrames
import Leanux.Proofs.WG.Index.ClearSource
import Leanux.Proofs.WG.Index.TimerFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem flushedSendPrepare_tables (pid : PeerId) :
    Ensures (flushedSendPrepare pid) TablesSafeWG (fun _ => TablesSafeWG) := by
  have dev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a result final after pre run
    cases device : g.dev with
    | none => simp [getDev,device,invariant,AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev,device] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      exact pre
  have peer : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g a result final after pre run).1
  have tail (p : Peer) : Ensures (do
      let d ← getDev
      setPeer pid {p with handshakePending := d.sendWorkQueue.contains pid})
      TablesSafeWG (fun _ => TablesSafeWG) := by
    refine ensures_bind _ _ dev ?_
    intro d
    exact (ensures_iff _ _ _).mpr (setPeer_tables pid _)
  unfold flushedSendPrepare
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (modifySendWorkQueue_tables (fun queue => queue.erase pid))) ?_
  intro _
  refine ensures_bind _ _ peer ?_
  intro p
  split
  · refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => tail p)
    exact (ensures_iff _ _ _).mpr
      (hoare_liftAmbient_variant (AmbientM.invariant "queued work without a pending flag") TablesSafeWG)
  · exact tail p

/-- Predicate-parametric composition of the original send-work flush. -/
theorem runFlushedSendWork_preserves (P : WGWorld → Prop) (pid : PeerId)
    (prepare : Ensures (flushedSendPrepare pid) P (fun _ => P))
    (worker : Ensures (handshakeSendWorker pid) P (fun _ => P)) :
    Ensures (runFlushedSendWork pid) P (fun _ => P) := by
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  rw [runFlushedSendWork_factor]
  refine ensures_bind _ _ prepare (fun _ => ?_)
  refine ensures_bind _ _ (ambient (AmbientM.hidden (.sectionStart .sendWorker))) (fun _ => ?_)
  refine ensures_bind _ _ worker (fun _ => ?_)
  refine ensures_bind _ _ (ambient (AmbientM.hidden (.sectionStop .sendWorker))) (fun _ => ?_)
  intro w a result v b hi run
  cases run
  exact hi

theorem runFlushedClearWork_preserves (P : WGWorld → Prop) (pid : PeerId)
    (dequeue : Ensures (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}) P (fun _ => P))
    (worker : Ensures (queuedExpiredZeroKeyMaterial pid) P (fun _ => P)) :
    Ensures (runFlushedClearWork pid) P (fun _ => P) := by
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  unfold runFlushedClearWork
  refine ensures_bind _ _ dequeue ?_
  intro _
  refine ensures_bind _ _ (ambient (AmbientM.hidden (.sectionStart .clearPeerWorker))) ?_
  intro _
  refine ensures_bind _ _ worker ?_
  intro _
  refine ensures_bind _ _ (ambient (AmbientM.hidden (.sectionStop .clearPeerWorker))) ?_
  intro _ g inputs result final after pre run
  cases run
  exact pre

/-- The original bounded drain, including named selection, placeholder order,
early return at the requested clear work, and its original stopped outcomes. -/
theorem drainHandshakeSendWq_preserves (P : WGWorld → Prop)
    (send : ∀ pid, Ensures (runFlushedSendWork pid) P (fun _ => P))
    (clear : ∀ pid, Ensures (runFlushedClearWork pid) P (fun _ => P))
    (upTo : Option PeerId) :
    Ensures (drainHandshakeSendWq upTo) P (fun _ => P) := by
  have pureValue {α : Type} (value : α) :
      Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have dev : Ensures getDev P (fun _ => P) := by
    intro g inputs result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have listFrame {α β : Type} (xs : List α) (initial : β)
      (body : α → β → WG.M (ForInStep β))
      (step : ∀ a b, Ensures (body a b) P (fun _ => P)) :
      Ensures (forIn xs initial body) P (fun _ => P) := by
    induction xs generalizing initial with
    | nil => simpa only [List.forIn_nil] using pureValue initial
    | cons x xs ih =>
      rw [List.forIn_cons]
      refine ensures_bind _ _ (step x initial) ?_
      intro result
      cases result with
      | done final => exact pureValue final
      | yield next => exact ih next
  have peek (worker : Worker) : Ensures (peekUnit worker : WG.M (Option Nat))
      P (fun _ => P) := ambient (AmbientM.peekUnit worker)
  have resolve (worker : Worker) (unit : Nat) (queue : List Nat) :
      Ensures (resolveUnit worker unit queue : WG.M Nat) P (fun _ => P) :=
    ambient (AmbientM.resolveUnit worker unit queue)
  have inputs : Ensures (getAmbient : WG.M Ambient) P (fun _ => P) :=
    ambient (get : AmbientM Ambient)
  have stop {α : Type} (reason : Stop) :
      Ensures (throw reason : WG.M α) P (fun _ => P) := by
    intro g a result final after pre run
    cases run
  have inv {α : Type} (what : String) :
      Ensures (invariant what : WG.M α) P (fun _ => P) :=
    ambient (AmbientM.invariant what)
  unfold drainHandshakeSendWq
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine ensures_bind (Q := fun _ => P) _ _ (listFrame _ _ _ ?_) ?_
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
      | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
      | split
  · rintro ⟨returned, _⟩
    cases returned with
    | none => exact inv _
    | some value => exact pureValue value

/-- Timer deletion and the actual conditional clear-work flush. -/
theorem timersStop_preserves (P : WGWorld → Prop)
    (deleted : ∀ pid timer, Ensures (delTimer pid timer) P (fun _ => P))
    (drain : ∀ upTo, Ensures (drainHandshakeSendWq upTo) P (fun _ => P)) (pid : PeerId) :
    Ensures (timersStop pid) P (fun _ => P) := by
  have pureValue {α : Type} (value : α) :
      Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have dev : Ensures getDev P (fun _ => P) := by
    intro g inputs result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  unfold timersStop
  simp only [PeerTimer.all, List.forIn_cons, List.forIn_nil, bind_assoc, pure_bind]
  repeat' first
    | exact pureValue _
    | exact dev
    | exact deleted pid _
    | exact drain _
    | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | split

/-- Actual ordered key releases, both flushes, accounting and final peer release.
The deadness guard remains operational; this contract does not assume it succeeds. -/
theorem peerRemoveAfterDead_preserves (P : WGWorld → Prop)
    (keys : ∀ pid, Ensures (keypairsClear pid) P (fun _ => P))
    (timers : ∀ pid, Ensures (timersStop pid) P (fun _ => P))
    (drain : ∀ upTo, Ensures (drainHandshakeSendWq upTo) P (fun _ => P))
    (decrement : Ensures (modifyDev fun d => {d with numPeers := d.numPeers-1}) P (fun _ => P))
    (release : ∀ pid, Ensures (peerPut (some pid)) P (fun _ => P)) (pid : PeerId) :
    Ensures (peerRemoveAfterDead pid) P (fun _ => P) := by
  have pureValue {α : Type} (value : α) :
      Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have dev : Ensures getDev P (fun _ => P) := by
    intro g inputs result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have peer : Ensures (getPeer pid) P (fun _ => P) := by
    intro g inputs result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P)
      g inputs result final after pre run).1
  have branch (site : Decision) (value : Bool) : Ensures (Leanux.branch site value : WG.M Bool)
      P (fun _ => P) := ambient (AmbientM.branch site value)
  have inv {α : Type} (what : String) : Ensures (invariant what : WG.M α)
      P (fun _ => P) := ambient (AmbientM.invariant what)
  have unsupportedStep {α : Type} (what : String) : Ensures (unsupported what : WG.M α)
      P (fun _ => P) := ambient (AmbientM.unsupported what)
  unfold peerRemoveAfterDead
  repeat' first
    | exact pureValue _
    | exact dev
    | exact peer
    | exact branch _ _
    | exact inv _
    | exact unsupportedStep _
    | exact keys pid
    | exact timers _
    | exact drain _
    | exact decrement
    | exact release pid
    | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | split

/-- Existing table contracts are instances of the single source composition. -/
theorem runFlushedSendWork_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ runFlushedSendWork pid ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (runFlushedSendWork_preserves TablesSafeWG pid
    (flushedSendPrepare_tables pid) (handshakeSendWorker_tables pid))

theorem runFlushedClearWork_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ runFlushedClearWork pid ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ :=
  (ensures_iff _ _ _).mp (runFlushedClearWork_preserves TablesSafeWG pid
    ((ensures_iff _ _ _).mpr (modifyClearWorkQueue_tables (fun queue => queue.erase pid)))
    (queuedExpiredZeroKeyMaterial_tables pid))

theorem drainHandshakeSendWq_tables (upTo : Option PeerId) :
    Ensures (drainHandshakeSendWq upTo) TablesSafeWG (fun _ => TablesSafeWG) :=
  drainHandshakeSendWq_preserves TablesSafeWG
    (fun pid => (ensures_iff _ _ _).mpr (runFlushedSendWork_tables pid))
    (fun pid => (ensures_iff _ _ _).mpr (runFlushedClearWork_tables pid)) upTo

theorem timersStop_tables (pid : PeerId) :
    Ensures (timersStop pid) TablesSafeWG (fun _ => TablesSafeWG) :=
  timersStop_preserves TablesSafeWG
    (fun pid timer => (ensures_iff _ _ _).mpr (delTimer_tables pid timer)) drainHandshakeSendWq_tables pid

theorem peerRemoveAfterDead_tables (pid : PeerId) :
    Ensures (peerRemoveAfterDead pid) TablesSafeWG (fun _ => TablesSafeWG) :=
  peerRemoveAfterDead_preserves TablesSafeWG
    (fun pid => (ensures_iff _ _ _).mpr (keypairsClear_tables pid))
    timersStop_tables drainHandshakeSendWq_tables
    ((ensures_iff _ _ _).mpr decrementNumPeers_tables)
    (fun pid => (ensures_iff _ _ _).mpr (peerPut_tables (some pid))) pid

end Leanux.Proofs.WG.Index
