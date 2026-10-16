import Leanux.Proofs.WG.Queues.TxDisposition

/-! Direct projection of the joint source observer. Unconditional suffix
lemmas for the reused primitive observers avoid assuming allocation validity
at intermediate setters. Completion's existing AllocationInv contract is
kept separate; no all-input safety claim follows from these equalities. -/
set_option maxHeartbeats 1500000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.TxDisposition
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

theorem getPeer_appends (id : PeerId) : StateAppends (getPeerMixed id) := StateAppends.focus _ _ _
theorem setPeer_appends (id : PeerId) (p : Peer) : StateAppends (setPeerMixed id p) := StateAppends.focus _ _ _
theorem peerGet_appends (id : PeerId) : StateAppends (peerGetMixed id) := StateAppends.focus _ _ _
theorem peerPut_appends (id : Option PeerId) : StateAppends (peerPutMixed id) := StateAppends.focus _ _ _
theorem keyGet_appends (id : KeypairId) : StateAppends (getKeypairPrefix id) := by
  intro w ambient h
  change ∃ suffix, (runStatePrefix (getKeypairPrefix id) w ambient h).2 = h ++ suffix
  rw [getKeypairPrefix_run]
  split
  · exact ⟨[], by simp⟩
  · exact ⟨_, rfl⟩
theorem ownerDeref_appends (owner : IndexOwner) : StateAppends (peerDerefPrefix owner) := by
  unfold peerDerefPrefix
  apply StateAppends.bind
  · cases owner <;> unfold peerWordPrefix
    all_goals apply StateAppends.bind
    all_goals first | exact getPeer_appends _ | exact keyGet_appends _ | intro x; exact StateAppends.pure _
  · intro word
    cases word <;> first | exact StateAppends.lift _ | exact StateAppends.pure _

theorem txGet_appends (id : SkbId) : StateAppends (getTxSkbPrefix id) := by
  intro w ambient h
  change ∃ suffix, (runStatePrefix (getTxSkbPrefix id) w ambient h).2 = h ++ suffix
  rw [getTxSkbPrefix_run]
  split
  · exact ⟨[], by simp⟩
  · exact ⟨_, rfl⟩
theorem txSet_appends (id : SkbId) (f : DataPacket → DataPacket) : StateAppends (setTxSkbPrefix id f) := by
  intro w ambient h
  change ∃ suffix, (runStatePrefix (setTxSkbPrefix id f) w ambient h).2 = h ++ suffix
  rw [setTxSkbPrefix_run]
  split
  · exact ⟨[], by simp⟩
  · exact ⟨_, rfl⟩
theorem txFree_appends (id : SkbId) : StateAppends (freeTxSkbPrefix id) := by
  intro w ambient h
  change ∃ suffix, (runStatePrefix (freeTxSkbPrefix id) w ambient h).2 = h ++ suffix
  rw [freeTxSkbPrefix_run]
  split
  · exact ⟨[], by simp⟩
  · exact ⟨_, rfl⟩
theorem keyPut_appends (id : Option KeypairId) (unreference : Bool) :
    StateAppends (keypairPutPrefix id unreference) := by
  intro w ambient h
  exact ⟨_, keypairPutPrefix_events id unreference w ambient h⟩
/-- Appended suffixes compose through a loop over the actual nested state. -/
theorem stateAppends_forIn {E Outer Inner α β : Type} (xs : List α) (init : β)
    (f : α → β → StatePrefixT E Outer Inner (ForInStep β))
    (hf : ∀ x b, StateAppends (f x b)) : StateAppends (forIn xs init f) := by
  induction xs generalizing init with
  | nil => exact StateAppends.pure _
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply StateAppends.bind (hf x init)
    intro step
    cases step with
    | done b => exact StateAppends.pure _
    | yield b => exact ih b

theorem cpu_appends (pid : PeerId) : StateAppends (cpumaskChooseOnlinePrefix pid) := by
  have range_appends {β : Type} (r : Std.Legacy.Range) (b : β)
      (f : Nat → β → MixedM (ForInStep β)) (hf : ∀ x b, StateAppends (f x b)) :
      StateAppends (forIn r b f) := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    exact stateAppends_forIn _ b f hf
  unfold cpumaskChooseOnlinePrefix
  repeat' first
    | exact getPeer_appends _
    | exact setPeer_appends _ _
    | exact StateAppends.lift _
    | exact StateAppends.pure _
    | apply range_appends
    | apply StateAppends.bind
    | (split)
    | (intro x; try dsimp only [id])

theorem access_project {S α : Type} {a : PrefixT LifetimeEvent S α} (ha : Appends a) : ProjectsPrefix accessEvent id (access a) a :=
  ha.project_focus _ _ (fun _ => rfl)

theorem nativeAccess_project (ha : StateAppends a) :
    ProjectsPrefix accessEvent id (nativeAccess a) (liftWGObserver a) :=
  access_project ha.liftWGObserver

theorem cut_project {S : Type} (ρ : Event → Option F) (e : Event) (he : ρ e = none) :
    ProjectsPrefix ρ id (emitPrefix e : PrefixT Event S Unit) (pure ()) := by
  simpa only [he, Option.elim_none] using projectsPrefix_emit ρ e

theorem cut_bind_project (ρ : Event → Option F) (e : Event) (he : ρ e = none)
    (hp : ProjectsPrefix ρ id (g : Obs α) (a : PrefixM F α)) : ProjectsPrefix ρ id (do emitPrefix e; g) a := by
  simpa only [pure_bind] using projectsPrefix_bind ρ id id
    (f := fun _ : Unit => g) (b := fun _ : Unit => a) (cut_project ρ e he) (fun _ => hp)

theorem project_pure {S : Type} (ρ : Event → Option F) (x : α) :
    ProjectsPrefix ρ id (pure x : PrefixT Event S α) (pure x) := by intro w h; rfl

theorem project_forIn (ρ : Event → Option F) (xs : List γ) (b : β)
    (g : γ → β → Obs (ForInStep β)) (a : γ → β → PrefixM F (ForInStep β))
    (ha : ∀ x b, ProjectsPrefix ρ id (g x b) (a x b)) :
    ProjectsPrefix ρ id (forIn xs b g) (forIn xs b a) := by
  induction xs generalizing b with
  | nil => exact project_pure ρ b
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply projectsPrefix_bind ρ id id (ha x b)
    intro step
    cases step with
    | done b => exact project_pure ρ b
    | yield b => exact ih b

theorem enqueueCore_access (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix accessEvent id (enqueueCore pid item) (liftWGObserver (enqueuePerDeviceAndPeerPrefix pid item)) := by
  unfold enqueueCore enqueuePerDeviceAndPeerPrefix
  cases hh : item.head? <;> simp only [hh, liftWGObserver_bind, liftWGObserver_pure,
    liftWGObserver_lift, liftWGObserver_forIn, apply_ite]
  repeat' first
    | with_reducible exact nativeAccess_project (txSet_appends _ _)
    | with_reducible exact nativeAccess_project (getPeer_appends _)
    | with_reducible exact nativeAccess_project (setPeer_appends _ _)
    | with_reducible exact projectsPrefix_lift _ _
    | exact project_pure _ _
    | with_reducible apply cut_bind_project _ _ rfl
    | with_reducible apply projectsPrefix_bind accessEvent id id
    | with_reducible apply projectsPrefix_ite
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only [id])

theorem enqueue_access (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix accessEvent id (enqueue pid item) (liftWGObserver (enqueuePerDeviceAndPeerPrefix pid item)) := by
  have ht (ret : Int) : ProjectsPrefix accessEvent id
      (do if ret = 0 then emitPrefix (.ring (.offered item true))
          else if ret = -WG.EPIPE then emitPrefix (.ring (.offered item false))
          pure ret : Obs Int) (pure ret) := by
    intro w h
    split <;> try split
    all_goals simp only [map_eq_pure_bind, runPrefix_bind, runPrefix_emit, runPrefix_pure, accessEvent, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil, Except.map, id]
  simpa only [enqueue, bind_pure] using projectsPrefix_bind accessEvent id id (enqueueCore_access pid item) ht

theorem publish_access (item : List SkbId) (state : PacketState) :
    ProjectsPrefix accessEvent id (publish item state) (liftWGObserver (enqueuePerPeerTxPrefix item state)) := by
  unfold publish enqueuePerPeerTxPrefix
  cases hh : item.head? <;> simp only [hh, liftWGObserver_bind, liftWGObserver_pure,
    liftWGObserver_lift, liftWGObserver_forIn, apply_ite]
  repeat' first
    | with_reducible exact nativeAccess_project (txGet_appends _)
    | with_reducible exact nativeAccess_project (ownerDeref_appends _)
    | with_reducible exact nativeAccess_project (peerGet_appends _)
    | with_reducible exact nativeAccess_project (getPeer_appends _)
    | with_reducible exact nativeAccess_project (txSet_appends _ _)
    | with_reducible exact nativeAccess_project (cpu_appends _)
    | with_reducible exact nativeAccess_project (peerPut_appends _)
    | with_reducible exact projectsPrefix_lift _ _
    | exact project_pure _ _
    | with_reducible apply cut_bind_project _ _ rfl
    | with_reducible apply projectsPrefix_bind accessEvent id id
    | with_reducible apply projectsPrefix_ite
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only [id])

theorem create_access (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix accessEvent id (create pid item) (liftWGObserver (createDataPrefix pid item)) := by
  unfold create createDataPrefix
  cases hh : item.head? <;> simp only [hh, liftWGObserver_bind, liftWGObserver_pure,
    liftWGObserver_lift, liftWGObserver_forIn, apply_ite]
  repeat' first
    | with_reducible exact enqueue_access _ _
    | with_reducible exact publish_access _ _
    | with_reducible exact nativeAccess_project (getPeer_appends _)
    | with_reducible exact nativeAccess_project (txGet_appends _)
    | with_reducible exact nativeAccess_project (keyPut_appends _ _)
    | with_reducible exact nativeAccess_project (peerPut_appends _)
    | with_reducible exact nativeAccess_project (txFree_appends _)
    | with_reducible exact projectsPrefix_lift _ _
    | exact project_pure _ _
    | with_reducible apply project_forIn accessEvent
    | with_reducible apply projectsPrefix_bind accessEvent id id
    | with_reducible apply projectsPrefix_ite
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only [id])

theorem access_history {S : Type} (ρ : Event → Option F) (hd : ∀ e, ρ (.access e) = none)
    (a : PrefixT LifetimeEvent S α) : HistoryFrame ρ (access a) :=
  fun w h => focusPrefix_other _ _ _ hd a w h

theorem enqueueCore_ring (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix ringEvent id (enqueueCore pid item) (liftPrefix (liftWG (enqueuePerDeviceAndPeer pid item))) := by
  apply HistoryFrame.project _ (enqueueCore_erases pid item)
  unfold enqueueCore nativeAccess
  repeat' first
    | with_reducible exact access_history _ (fun _ => rfl) _
    | with_reducible exact HistoryFrame.lift _ _
    | with_reducible exact HistoryFrame.pure _ _
    | with_reducible exact HistoryFrame.emit _ rfl
    | with_reducible apply HistoryFrame.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem enqueue_ring (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix ringEvent id (enqueue pid item) (TxRing.enqueue pid item) := by
  unfold enqueue TxRing.enqueue Ring.Source.enqueue
  apply projectsPrefix_bind ringEvent id id (enqueueCore_ring pid item)
  intro ret
  dsimp only [id]
  simp only [WG.EPIPE, EPIPE]
  by_cases hz : ret = 0
  · simp only [hz, ↓reduceIte]
    apply projectsPrefix_bind ringEvent id id (projectsPrefix_emit ringEvent _)
    intro _
    exact project_pure _ _
  · simp only [hz, ↓reduceIte]
    by_cases hp : ret = -32
    · simp only [hp, ↓reduceIte]
      apply projectsPrefix_bind ringEvent id id (projectsPrefix_emit ringEvent _)
      intro _
      exact project_pure _ _
    · simp only [hp, ↓reduceIte]
      exact project_pure _ _

theorem publish_ring_frame (item : List SkbId) (state : PacketState) : HistoryFrame ringEvent (publish item state) := by
  unfold publish nativeAccess
  repeat' first
    | with_reducible exact access_history _ (fun _ => rfl) _
    | with_reducible exact HistoryFrame.lift _ _
    | with_reducible exact HistoryFrame.pure _ _
    | with_reducible exact HistoryFrame.emit _ rfl
    | with_reducible apply HistoryFrame.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem create_ring (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix ringEvent id (create pid item) (TxRing.create pid item) := by
  unfold create TxRing.create nativeAccess
  cases hh : item.head? <;> simp only [hh, liftWGObserver_bind, liftWGObserver_pure,
    liftWGObserver_lift, liftWGObserver_forIn, apply_ite]
  repeat' first
    | with_reducible exact enqueue_ring _ _
    | with_reducible exact (publish_ring_frame _ _).project (publish_erases _ _)
    | with_reducible exact access_ring (liftWGObserver_erases (getPeerMixed_erases _))
    | with_reducible exact access_ring (liftWGObserver_erases (getTxSkbPrefix_erases _))
    | with_reducible exact access_ring (liftWGObserver_erases (keypairPutPrefix_erases _ _))
    | with_reducible exact access_ring (liftWGObserver_erases (peerPutMixed_erases _))
    | with_reducible exact access_ring (liftWGObserver_erases (freeTxSkbPrefix_erases _))
    | with_reducible exact projectsPrefix_lift _ _
    | exact project_pure _ _
    | with_reducible apply project_forIn ringEvent
    | with_reducible apply projectsPrefix_bind ringEvent id id
    | with_reducible apply projectsPrefix_ite
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only [id])

end Leanux.Proofs.WG.Queues.TxDisposition
