import Leanux.Proofs.WG.Queues.TxDisposition

/-! Direct projection of the joint source observer. Unconditional suffix
lemmas for the reused primitive observers avoid assuming allocation validity
at intermediate setters. Completion's existing AllocationInv contract is
kept separate; no all-input safety claim follows from these equalities. -/
set_option maxHeartbeats 1500000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.TxDisposition
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

theorem getPeer_appends (id : PeerId) : Appends (getPeerMixed id) := Appends.focus _ _ _
theorem setPeer_appends (id : PeerId) (p : Peer) : Appends (setPeerMixed id p) := Appends.focus _ _ _
theorem peerGet_appends (id : PeerId) : Appends (peerGetMixed id) := Appends.focus _ _ _
theorem peerPut_appends (id : Option PeerId) : Appends (peerPutMixed id) := Appends.focus _ _ _
theorem keyGet_appends (id : KeypairId) : Appends (getKeypairPrefix id) := by
  intro w h
  rw [getKeypairPrefix_run]
  split
  · exact ⟨[], by simp⟩
  · exact ⟨_, rfl⟩
theorem txGet_appends (id : SkbId) : Appends (getTxSkbPrefix id) := by
  intro w h
  rw [getTxSkbPrefix_run]
  split
  · exact ⟨[], by simp⟩
  · exact ⟨_, rfl⟩
theorem txSet_appends (id : SkbId) (f : DataPacket → DataPacket) : Appends (setTxSkbPrefix id f) := by
  intro w h
  rw [setTxSkbPrefix_run]
  split
  · exact ⟨[], by simp⟩
  · exact ⟨_, rfl⟩
theorem txFree_appends (id : SkbId) : Appends (freeTxSkbPrefix id) := by
  intro w h
  rw [freeTxSkbPrefix_run]
  split
  · exact ⟨[], by simp⟩
  · exact ⟨_, rfl⟩
theorem keyPut_appends (id : Option KeypairId) (unreference : Bool) :
    Appends (keypairPutPrefix id unreference) := by
  intro w h
  exact ⟨_, keypairPutPrefix_events id unreference w h⟩
theorem cpu_appends (pid : PeerId) : Appends (cpumaskChooseOnlinePrefix pid) := by
  unfold cpumaskChooseOnlinePrefix
  repeat' first
    | with_reducible exact getPeer_appends _
    | with_reducible exact setPeer_appends _ _
    | with_reducible exact Appends.lift _
    | with_reducible exact Appends.pure _
    | with_reducible apply Appends.range
    | with_reducible apply Appends.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only [id])

theorem access_project (ha : Appends a) : ProjectsPrefix accessEvent id (access a) a :=
  ha.project_focus _ _ (fun _ => rfl)

theorem cut_project (ρ : Event → Option F) (e : Event) (he : ρ e = none) :
    ProjectsPrefix ρ id (emitPrefix e) (pure ()) := by
  simpa only [he, Option.elim_none] using projectsPrefix_emit ρ e

theorem cut_bind_project (ρ : Event → Option F) (e : Event) (he : ρ e = none)
    (hp : ProjectsPrefix ρ id (g : Obs α) (a : PrefixM F α)) : ProjectsPrefix ρ id (do emitPrefix e; g) a := by
  simpa only [pure_bind] using projectsPrefix_bind ρ id id
    (f := fun _ : Unit => g) (b := fun _ : Unit => a) (cut_project ρ e he) (fun _ => hp)

theorem project_pure (ρ : Event → Option F) (x : α) :
    ProjectsPrefix ρ id (pure x) (pure x) := by intro w h; rfl

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
    ProjectsPrefix accessEvent id (enqueueCore pid item) (enqueuePerDeviceAndPeerPrefix pid item) := by
  unfold enqueueCore enqueuePerDeviceAndPeerPrefix
  cases hh : item.head? <;> simp only [hh]
  repeat' first
    | with_reducible exact access_project (txSet_appends _ _)
    | with_reducible exact access_project (getPeer_appends _)
    | with_reducible exact access_project (setPeer_appends _ _)
    | with_reducible exact projectsPrefix_lift _ _
    | exact project_pure _ _
    | with_reducible apply cut_bind_project _ _ rfl
    | with_reducible apply projectsPrefix_bind accessEvent id id
    | with_reducible apply projectsPrefix_ite
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only [id])

theorem enqueue_access (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix accessEvent id (enqueue pid item) (enqueuePerDeviceAndPeerPrefix pid item) := by
  have ht (ret : Int) : ProjectsPrefix accessEvent id
      (do if ret = 0 then emitPrefix (.ring (.offered item true))
          else if ret = -WG.EPIPE then emitPrefix (.ring (.offered item false))
          pure ret : Obs Int) (pure ret) := by
    intro w h
    split <;> try split
    all_goals simp only [map_eq_pure_bind, runPrefix_bind, runPrefix_emit, runPrefix_pure, accessEvent, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil, Except.map, id]
  simpa only [enqueue, bind_pure] using projectsPrefix_bind accessEvent id id (enqueueCore_access pid item) ht

theorem publish_access (item : List SkbId) (state : PacketState) :
    ProjectsPrefix accessEvent id (publish item state) (enqueuePerPeerTxPrefix item state) := by
  unfold publish enqueuePerPeerTxPrefix
  cases hh : item.head? <;> simp only [hh]
  repeat' first
    | with_reducible exact access_project (txGet_appends _)
    | with_reducible exact access_project (keyGet_appends _)
    | with_reducible exact access_project (peerGet_appends _)
    | with_reducible exact access_project (getPeer_appends _)
    | with_reducible exact access_project (txSet_appends _ _)
    | with_reducible exact access_project (cpu_appends _)
    | with_reducible exact access_project (peerPut_appends _)
    | with_reducible exact projectsPrefix_lift _ _
    | exact project_pure _ _
    | with_reducible apply cut_bind_project _ _ rfl
    | with_reducible apply projectsPrefix_bind accessEvent id id
    | with_reducible apply projectsPrefix_ite
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only [id])

theorem create_access (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix accessEvent id (create pid item) (createDataPrefix pid item) := by
  unfold create createDataPrefix
  cases hh : item.head? <;> simp only [hh]
  repeat' first
    | with_reducible exact enqueue_access _ _
    | with_reducible exact publish_access _ _
    | with_reducible exact access_project (getPeer_appends _)
    | with_reducible exact access_project (txGet_appends _)
    | with_reducible exact access_project (keyPut_appends _ _)
    | with_reducible exact access_project (peerPut_appends _)
    | with_reducible exact access_project (txFree_appends _)
    | with_reducible exact projectsPrefix_lift _ _
    | exact project_pure _ _
    | with_reducible apply project_forIn accessEvent
    | with_reducible apply projectsPrefix_bind accessEvent id id
    | with_reducible apply projectsPrefix_ite
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only [id])

theorem access_history (ρ : Event → Option F) (hd : ∀ e, ρ (.access e) = none)
    (a : MixedM α) : HistoryFrame ρ (access a) :=
  fun w h => focusPrefix_other _ _ _ hd a w h

theorem enqueueCore_ring (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix ringEvent id (enqueueCore pid item) (liftPrefix (enqueuePerDeviceAndPeer pid item)) := by
  apply HistoryFrame.project _ (enqueueCore_erases pid item)
  unfold enqueueCore
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
  unfold publish
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
  unfold create TxRing.create
  cases hh : item.head? <;> simp only [hh]
  repeat' first
    | with_reducible exact enqueue_ring _ _
    | with_reducible exact (publish_ring_frame _ _).project (publish_erases _ _)
    | with_reducible exact access_ring (getPeerMixed_erases _)
    | with_reducible exact access_ring (getTxSkbPrefix_erases _)
    | with_reducible exact access_ring (keypairPutPrefix_erases _ _)
    | with_reducible exact access_ring (peerPutMixed_erases _)
    | with_reducible exact access_ring (freeTxSkbPrefix_erases _)
    | with_reducible exact projectsPrefix_lift _ _
    | exact project_pure _ _
    | with_reducible apply project_forIn ringEvent
    | with_reducible apply projectsPrefix_bind ringEvent id id
    | with_reducible apply projectsPrefix_ite
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only [id])

end Leanux.Proofs.WG.Queues.TxDisposition
