import Leanux.Proofs.WG.AuthenticatedEffects.TimerRootSource

/-! The arm observer projects to the already-checked complete receiver journal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerRoot
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def Projects (g : WGPrefix Event α) (a : WGPrefix HandshakeCausal.Event α) : Prop :=
  ∀ w ambient h, runWGPrefix a w ambient (history h) =
    ((runWGPrefix g w ambient h).1,history (runWGPrefix g w ambient h).2)

theorem projects_bind (g : WGPrefix Event α) (a : WGPrefix HandshakeCausal.Event α)
    (next : α → WGPrefix Event β) (tail : α → WGPrefix HandshakeCausal.Event β)
    (hg : Projects g a) (hn : ∀ x, Projects (next x) (tail x)) :
    Projects (g >>= next) (a >>= tail) := by
  intro w ambient h
  change runStatePrefix (a >>= tail) w ambient (history h) = _
  have he := hg w ambient h
  simp only [runWGPrefix] at he
  rw [runStatePrefix_bind,he]
  change _ = ((runStatePrefix (g >>= next) w ambient h).1,history (runStatePrefix (g >>= next) w ambient h).2)
  rw [runStatePrefix_bind]
  cases hr : runStatePrefix g w ambient h with
  | mk result hist =>
    cases result with
    | error err => rfl
    | ok out => rcases out with ⟨⟨x,v⟩,b⟩; exact hn x v b hist

theorem projects_pure (x : α) : Projects (pure x) (pure x) := by intro w a h; rfl
theorem projects_lift (a : WG.M α) : Projects (liftWGPrefix a) (liftWGPrefix a) := by intro w ambient h; rfl
theorem projects_choice (p : Prop) [Decidable p]
    (g k : WGPrefix Event α) (a b : WGPrefix HandshakeCausal.Event α)
    (hg : Projects g a) (hk : Projects k b) : Projects (if p then g else k) (if p then a else b) := by
  split <;> assumption

private theorem quiet (g : WGPrefix Event α) (a : WG.M α)
    (erases : ErasesStatePrefix g a) (frame : StateHistoryFrame base g) :
    Projects g (liftWGPrefix a) := by
  intro w ambient h
  apply Prod.ext
  · exact (erases w ambient h).symm
  · exact (frame w ambient h).symm

private theorem lift_erases (a : WG.M α) : ErasesStatePrefix (liftWGPrefix a : WGPrefix Event α) a :=
  erasesStatePrefix_lift a
private theorem lift_frame (a : WG.M α) : StateHistoryFrame base (liftWGPrefix a) := by intro w ambient h; rfl
private theorem pure_frame (x : α) : StateHistoryFrame base (pure x : WGPrefix Event α) := by intro w ambient h; rfl
private theorem frame_choice (p : Prop) [Decidable p] (a b : WGPrefix Event α)
    (ha : StateHistoryFrame base a) (hb : StateHistoryFrame base b) :
    StateHistoryFrame base (if p then a else b) := by split <;> assumption

private theorem arm_erases (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    ErasesStatePrefix (arm origin kind pid timer delay caller) (armTimer pid timer delay caller) :=
  receiptWGObserved_erases (lift_erases _) _
private theorem arm_frame (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    StateHistoryFrame base (arm origin kind pid timer delay caller) :=
  StateHistoryFrame.receiptWGObserved (lift_frame _) _ (fun _ => rfl)

private theorem modify_erases (origin : Nat) (kind : HandshakeCausal.Kind) (site : HiddenSite)
    (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    ErasesStatePrefix (modifyTimer origin kind site pid timer delay) (modPeerTimer site pid timer delay) := by
  unfold modifyTimer modPeerTimer
  apply erasesStatePrefix_bind (lift_erases _)
  intro jc
  apply erasesStatePrefix_bind (lift_erases _)
  intro guard
  split
  · exact erasesStatePrefix_bind (arm_erases _ _ _ _ _ _) (fun _ => erasesStatePrefix_pure _)
  · exact erasesStatePrefix_pure _
private theorem modify_frame (origin : Nat) (kind : HandshakeCausal.Kind) (site : HiddenSite)
    (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    StateHistoryFrame base (modifyTimer origin kind site pid timer delay) := by
  unfold modifyTimer
  apply StateHistoryFrame.bind (lift_frame _)
  intro jc
  apply StateHistoryFrame.bind (lift_frame _)
  intro guard
  split
  · exact StateHistoryFrame.bind (arm_frame _ _ _ _ _ _) (fun _ => pure_frame _)
  · exact pure_frame _

theorem derived_erases (origin : Nat) (pid : PeerId) :
    ErasesStatePrefix (derived origin pid) (timersSessionDerived pid) := by
  unfold derived timersSessionDerived
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  exact erasesStatePrefix_bind (modify_erases _ _ _ _ _ _) (fun _ => erasesStatePrefix_pure _)
theorem derived_frame (origin : Nat) (pid : PeerId) : StateHistoryFrame base (derived origin pid) := by
  unfold derived
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  exact StateHistoryFrame.bind (modify_frame _ _ _ _ _ _) (fun _ => pure_frame _)

theorem traversal_erases (origin : Nat) (pid : PeerId) :
    ErasesStatePrefix (traversal origin pid) (timersTraversal pid) := by
  unfold traversal timersTraversal
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  apply erasesStatePrefix_bind (lift_erases _)
  intro peer
  apply erasesStatePrefix_bind (lift_erases _)
  intro guard
  split
  · exact erasesStatePrefix_bind (modify_erases _ _ _ _ _ _) (fun _ => erasesStatePrefix_pure _)
  · exact erasesStatePrefix_pure _
theorem traversal_frame (origin : Nat) (pid : PeerId) : StateHistoryFrame base (traversal origin pid) := by
  unfold traversal
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  apply StateHistoryFrame.bind (lift_frame _)
  intro peer
  apply StateHistoryFrame.bind (lift_frame _)
  intro guard
  split
  · exact StateHistoryFrame.bind (modify_frame _ _ _ _ _ _) (fun _ => pure_frame _)
  · exact pure_frame _

theorem call_projects (kind : HandshakeCausal.Kind) (pid : PeerId)
    (body : Nat → WGPrefix Event α) (native : WG.M α)
    (erases : ∀ origin, ErasesStatePrefix (body origin) native)
    (frame : ∀ origin, StateHistoryFrame base (body origin)) :
    Projects (call kind pid body) (HandshakeCausal.call kind pid native) := by
  intro w ambient h
  simp only [call,HandshakeCausal.call,runWGPrefix,runStatePrefix_bind,runStatePrefix_emit]
  change runStatePrefix (liftWGPrefix native) w ambient (history h ++ [.callback kind pid]) =
    ((runStatePrefix (body (history h).length) w ambient (h ++ [.base (.callback kind pid)])).1,
      history (runStatePrefix (body (history h).length) w ambient (h ++ [.base (.callback kind pid)])).2)
  have he := quiet (body (history h).length) native (erases _) (frame _) w ambient (h ++ [.base (.callback kind pid)])
  have hh : history (h ++ [.base (.callback kind pid)]) = history h ++ [.callback kind pid] := by
    simp [history,base]
  rw [hh] at he
  exact he

private theorem old_projects (a : WGPrefix HandshakeCausal.Event α) (append : StateAppends a) :
    Projects (old a) a := by
  intro w ambient h
  have hp := (append w).project_focus Event.base base (fun _ => rfl) ambient h
  have identity : (fun x : (α × WGWorld) × Ambient => (id x.1,x.2)) = id := by funext x; rfl
  rw [identity,Except.map_id] at hp
  exact hp

theorem old_call_projects (kind : HandshakeCausal.Kind) (pid : PeerId) (native : WG.M α) :
    Projects (old (HandshakeCausal.call kind pid native)) (HandshakeCausal.call kind pid native) := by
  apply old_projects
  apply StateAppends.bind
  · intro w ambient h; exact ⟨[.callback kind pid],rfl⟩
  · intro doneUnit; exact StateAppends.lift native
theorem old_initiation_projects (mac : HandshakeMac) :
    Projects (old (HandshakeCausal.initiation mac)) (HandshakeCausal.initiation mac) :=
  old_projects _ (StateAppends.focus _ _ _)
theorem old_response_projects (mac : HandshakeMac) :
    Projects (old (HandshakeCausal.response mac)) (HandshakeCausal.response mac) :=
  old_projects _ (StateAppends.focus _ _ _)

theorem derived_projects (pid : PeerId) :
    Projects (call .sessionDerived pid (fun origin => derived origin pid))
      (HandshakeCausal.call .sessionDerived pid (timersSessionDerived pid)) :=
  call_projects _ _ _ _ (fun _ => derived_erases _ _) (fun _ => derived_frame _ _)
theorem traversal_projects (pid : PeerId) :
    Projects (call .traversal pid (fun origin => traversal origin pid))
      (HandshakeCausal.call .traversal pid (timersTraversal pid)) :=
  call_projects _ _ _ _ (fun _ => traversal_erases _ _) (fun _ => traversal_frame _ _)

elab "timer_root_project_choice" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``Projects do Lean.throwError "expected a projection"
  let args := target.getAppArgs
  unless args[args.size - 2]!.isAppOf ``ite do Lean.throwError "expected an explicit choice"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply projects_choice))

theorem responseWith_projects (mac : HandshakeMac) (pid : PeerId) :
    Projects (responseWith (ops mac) pid) (responseWith (HandshakeCausal.ops mac) pid) := by
  unfold responseWith
  simp only [ops,HandshakeCausal.ops]
  repeat' first
    | with_reducible exact old_call_projects _ _ _
    | with_reducible exact derived_projects _
    | with_reducible exact traversal_projects _
    | with_reducible exact projects_lift _
    | with_reducible exact projects_pure _
    | with_reducible apply projects_bind
    | split
    | timer_root_project_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only [Option.some.injEq]

elab "timer_root_response_projects" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``Projects do Lean.throwError "expected a projection"
  let args := target.getAppArgs
  unless args[args.size - 2]!.isAppOf ``responseWith do Lean.throwError "expected a response sender"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact responseWith_projects _ _))

theorem afterMac_projects (mac : HandshakeMac) (msg : Key) (src : SkbSource)
    (loaded : Bool) (state : MacState) :
    Projects (afterMacWith (ops mac) msg src loaded state)
      (afterMacWith (HandshakeCausal.ops mac) msg src loaded state) := by
  unfold afterMacWith
  simp only [ops,HandshakeCausal.ops]
  repeat' first
    | timer_root_response_projects
    | with_reducible exact old_initiation_projects _
    | with_reducible exact old_response_projects _
    | with_reducible exact old_call_projects _ _ _
    | with_reducible exact derived_projects _
    | with_reducible exact traversal_projects _
    | with_reducible exact projects_lift _
    | with_reducible exact projects_pure _
    | with_reducible apply projects_bind
    | split
    | timer_root_project_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only [Option.some.injEq]

theorem capture_projects (a : WG.M α) : Projects (captureWGRun a) (captureWGRun a) := by
  intro w ambient h
  rw [runWGPrefix_captureWGRun,runWGPrefix_captureWGRun]

theorem receive_projects (msg : Key) (src : SkbSource) :
    Projects (receive msg src) (HandshakeCausal.receive msg src) := by
  unfold receive HandshakeCausal.receive
  apply projects_bind _ _ _ _ (projects_lift _)
  intro cookie
  split
  · exact projects_bind _ _ _ _ (projects_lift _) (fun _ => projects_pure _)
  · apply projects_bind _ _ _ _ (projects_lift _)
    intro loaded
    apply projects_bind _ _ _ _ (capture_projects _)
    intro checked
    exact afterMac_projects _ _ _ _ _

theorem receive_erases (msg : Key) (src : SkbSource) :
    ErasesStatePrefix (receive msg src) (receiveHandshakePacket msg src) := by
  intro w ambient h
  exact (congrArg Prod.fst (receive_projects msg src w ambient h)).symm.trans
    (HandshakeCausal.receive_erases msg src w ambient (history h))

end Leanux.Proofs.WG.AuthenticatedEffects.TimerRoot
