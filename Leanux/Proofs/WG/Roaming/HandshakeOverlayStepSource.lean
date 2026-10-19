import Leanux.Proofs.WG.Roaming.HandshakeOverlayReceptionSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeOverlay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Origins
variable {E F α State : Type}

def packetMessage (d : Device) : List UInt8 :=
  match d.handshakeQueue.consume.1 with
  | none => []
  | some (msg,_) => msg

def step : PrefixM Event Bool := do
  let d ← liftPrefix (liftWG getDev)
  HandshakeSources.stepWith (ops (packetMessage d))

theorem old_lift (action : Leanux.M α) :
    old (liftPrefix action) = liftPrefix action := by
  funext w h
  change (_,h ++ ((h.filterMap oldEvent).drop (h.filterMap oldEvent).length).map Sum.inl) = _
  simp only [List.drop_length,List.map_nil,List.append_nil]
  rfl

theorem getDev_run (w : World) :
    (liftWG getDev).run w =
      match w.wg.dev with
      | some d => .ok (d,w)
      | none => .error (.invariant "no WireGuard device in this trace's fixture") := by
  have native : (getDev.run w.wg).run w.ambient =
      match w.wg.dev with
      | some d => .ok ((d,w.wg),w.ambient)
      | none => .error (.invariant "no WireGuard device in this trace's fixture") := by
    cases hd : w.wg.dev with
    | none =>
      simp [getDev,hd,invariant,AmbientM.invariant]
      rfl
    | some d => simp [getDev,hd]
  rw [liftWG_run,native]
  cases w.wg.dev <;> rfl

theorem getDev_repeat (next : Device → PrefixM E α) :
    (liftPrefix (liftWG getDev) >>= fun _ => liftPrefix (liftWG getDev) >>= next) =
      (liftPrefix (liftWG getDev) >>= next) := by
  funext w h
  change runPrefix _ w h = runPrefix _ w h
  rw [runPrefix_bind,runPrefix_bind,runPrefix_lift,getDev_run]
  cases hd : w.wg.dev with
  | none => rfl
  | some d =>
    change runPrefix (liftPrefix (liftWG getDev) >>= next) w h = runPrefix (next d) w h
    rw [runPrefix_bind,runPrefix_lift,getDev_run,hd]

theorem localStep_peek :
    (do let _ ← liftPrefix (liftWG getDev); HistoryAdapters.localStep) =
      HistoryAdapters.localStep := by
  unfold HistoryAdapters.localStep HandshakeSources.stepWith
  exact getDev_repeat _

theorem step_old : ProjectsPrefix oldEvent id step HistoryAdapters.localStep := by
  rw [← localStep_peek]
  exact projectsPrefix_bind oldEvent id id
    (projectsPrefix_lift oldEvent (liftWG getDev))
    (fun d => HandshakeProjection.step_projects _ _ _ (ops_old (packetMessage d)))


theorem old_valid (action : PrefixM Origins.Event α) :
    PrefixPreserves (fun h _ => Valid h) Valid (old action) := by
  intro w h prior
  obtain ⟨suffix,same⟩ := Appends.focus Sum.inl oldEvent action w h
  have unchanged := focusPrefix_other Sum.inl oldEvent attemptEvent (fun _ => rfl) action w h
  have valid : Valid (runPrefix (old action) w h).2 := by
    unfold Valid old
    rw [unchanged]
    exact prior
  refine ⟨suffix,same,valid,?_⟩
  cases (runPrefix (old action) w h).1 <;> first | trivial | exact valid

theorem event_pure_valid (x : α) :
    PrefixPreserves (fun h _ => Valid h) Valid (pure x : PrefixM Event α) := by
  intro w h prior
  exact ⟨[],by simp,prior,prior⟩

theorem stepWith_valid (d : Device) :
    PrefixEnsures (fun h (w : World) => Valid h ∧ w.wg.dev = some d) Valid
      (HandshakeSources.stepWith (ops (packetMessage d))) (fun _ h _ => Valid h) := by
  unfold HandshakeSources.stepWith
  change PrefixEnsures _ _ (old (liftPrefix (liftWG getDev)) >>= _) _
  rw [old_lift]
  apply PrefixEnsures.bind (Q := fun actual h _ => Valid h ∧ actual = d)
  · apply PrefixEnsures.lift
    · exact fun _ _ h => h.1
    · intro h w actual final prior run
      rw [getDev_run,prior.2] at run
      cases run
      exact ⟨prior.1,rfl⟩
  · intro actual w h prior
    rcases prior with ⟨valid,equal⟩
    subst actual
    have body :
        PrefixPreserves (fun h _ => Valid h) Valid
          (match d.handshakeQueue.consume with
          | (none,_) => do
            let _ ← (ops (packetMessage d)).step (branch .workerConsumed false)
            pure false
          | (some (msg,src),ring) => do
            let _ ← (ops (packetMessage d)).step (branch .workerConsumed true)
            (ops (packetMessage d)).step (modifyDev fun d => {d with handshakeQueue := ring})
            HandshakeSources.receptionWith (ops (packetMessage d)) msg src
            (ops (packetMessage d)).step (modifyDev fun d => {d with handshakeQueueLen := d.handshakeQueueLen - 1})
            pure true) := by
      cases chosen : d.handshakeQueue.consume with
      | mk packet ring =>
        cases packet with
        | none =>
          exact (old_valid _).bind (fun _ => event_pure_valid false)
        | some packet =>
          rcases packet with ⟨msg,src⟩
          have selected : packetMessage d = msg := by simp only [packetMessage,chosen]
          rw [selected]
          exact (old_valid _).bind (fun _ =>
            (old_valid _).bind (fun _ =>
              (reception_valid msg src).bind (fun _ =>
                (old_valid _).bind (fun _ => event_pure_valid true))))
    exact body w h valid

theorem step_valid : PrefixPreserves (fun h _ => Valid h) Valid step := by
  unfold step
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (Q := fun d h w => Valid h ∧ w.wg.dev = some d)
  · apply PrefixEnsures.lift
    · exact fun _ _ h => h
    · intro h w d final prior run
      rw [getDev_run] at run
      cases present : w.wg.dev with
      | none => rw [present] at run; cases run
      | some actual =>
        rw [present] at run
        cases run
        exact ⟨prior,present⟩
  · exact stepWith_valid

theorem step_erases : ErasesPrefix step (liftWG receiveStep) := by
  intro w h
  have projected := step_old w h
  have erased := HistoryAdapters.localStep_erases w (h.filterMap oldEvent)
  have same := congrArg Prod.fst projected
  rw [erased] at same
  cases result : (runPrefix step w h).1 <;>
    simpa only [result,Except.map,id_eq] using same.symm

theorem step_attempts_valid (w : World) (h : List Event) (prior : Valid h) :
    ∀ r ∈ (runPrefix step w h).2.filterMap attemptEvent, Authenticated r := by
  obtain ⟨_,_,valid,_⟩ := step_valid w h prior
  exact valid


theorem stepWith_appends (label : List UInt8) :
    Appends (HandshakeSources.stepWith (ops label)) := by
  unfold HandshakeSources.stepWith
  dsimp only [ops]
  repeat' first
    | (overlay_action_head HandshakeSources.receptionWith; exact receptionWith_appends label _ _)
    | (overlay_action_head old; exact Appends.focus _ _ _)
    | (overlay_action_head Bind.bind; apply Appends.bind)
    | exact Appends.pure _
    | apply appends_ite
    | handshake_project_intro
    | split
theorem step_appends : Appends step :=
  (Appends.lift _).bind (fun d => stepWith_appends (packetMessage d))


end Leanux.Proofs.WG.Roaming.HandshakeOverlay
