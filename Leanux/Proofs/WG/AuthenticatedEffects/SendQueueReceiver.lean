import Leanux.Proofs.WG.AuthenticatedEffects.SendQueueReceiverFrames

/-! The complete native handshake receiver transports its concrete ordered
work-occurrence carrier. The callback journal remains the same source observer
used for authentication; this module adds its state invariant. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes TimerRoot
open Origins.HandshakeSources
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private theorem framed {g : WGPrefix Event α} {native : WG.M α}
    (erases : ErasesStatePrefix g native) (appends : StateAppends g)
    (frame : SameView queue native) : Preserves g := by
  intro w a h hi
  obtain ⟨tickets,carrier⟩ := hi
  obtain ⟨suffix,history⟩ := appends w a h
  refine ⟨suffix,history,True.intro,?_⟩
  cases outcome : (runPrefix (g.run w) a h).1 with
  | error err => trivial
  | ok out =>
    rcases out with ⟨⟨result,v⟩,b⟩
    have nativeRun := (erases w a h).symm.trans outcome
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp frame w a result v b nativeRun
    exact ⟨tickets,history.symm ▸ (carrier.frame same).append suffix⟩

private theorem old_preserves (g : WGPrefix HandshakeCausal.Event α) (native : WG.M α)
    (erases : ErasesStatePrefix g native) (frame : SameView queue native) : Preserves (old g) :=
  framed (focusStatePrefix_erases _ _ erases) (StateAppends.focus _ _ _) frame

private theorem old_call (kind : HandshakeCausal.Kind) (pid : PeerId) (native : WG.M α)
    (frame : SameView queue native) : Preserves (old (HandshakeCausal.call kind pid native)) :=
  old_preserves _ _ (HandshakeCausal.call_erases _ _ _) frame

private theorem old_initiation (mac : HandshakeMac) : Preserves (old (HandshakeCausal.initiation mac)) :=
  old_preserves _ _ (HandshakeCausal.initiation_erases mac) (initiation_frame mac.input)
private theorem old_response (mac : HandshakeMac) : Preserves (old (HandshakeCausal.response mac)) :=
  old_preserves _ _ (HandshakeCausal.response_erases mac) (response_frame mac.input)

private theorem enter_preserves (kind : HandshakeCausal.Kind) (pid : PeerId) : Preserves (enter kind pid) := by
  intro w a h hi
  obtain ⟨tickets,carrier⟩ := hi
  exact ⟨[.base (.callback kind pid)],rfl,True.intro,tickets,carrier.append _⟩

private theorem call_preserves (kind : HandshakeCausal.Kind) (pid : PeerId)
    (body : Nat → WGPrefix Event α) (hb : ∀ origin, Preserves (body origin)) : Preserves (call kind pid body) :=
  StatePrefixEnsures.bind (enter_preserves kind pid) hb

private theorem pure_preserves (x : α) : Preserves (pure x) :=
  StatePrefixEnsures.pure x (fun _ _ _ _ => True.intro) (fun _ _ _ hi => hi)
private theorem chain (g : WGPrefix Event α) (next : α → WGPrefix Event β)
    (hg : Preserves g) (hf : ∀ x, Preserves (next x)) : Preserves (g >>= next) := StatePrefixEnsures.bind hg hf
private theorem choice (p : Prop) [Decidable p] (a b : WGPrefix Event α)
    (ha : Preserves a) (hb : Preserves b) : Preserves (if p then a else b) := by split <;> assumption

private theorem arm_preserves (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) : Preserves (arm origin kind pid timer delay caller) :=
  framed_receipt_preserves _ _ (timer_arm_frame pid timer delay caller)

private theorem modify_preserves (origin : Nat) (kind : HandshakeCausal.Kind) (site : HiddenSite)
    (pid : PeerId) (timer : PeerTimer) (delay : Nat) : Preserves (modifyTimer origin kind site pid timer delay) := by
  unfold modifyTimer
  apply chain _ _ (lift_preserves ((callerJiffies_sameWGWorld site).of_factor queue queue (fun _ => rfl)))
  intro caller
  apply chain _ _ (lift_preserves (timer_guard_frame pid))
  intro ready
  split
  · exact chain _ _ (arm_preserves _ _ _ _ _ _) (fun _ => pure_preserves _)
  · exact pure_preserves _

private theorem derived_preserves (origin : Nat) (pid : PeerId) : Preserves (derived origin pid) := by
  unfold derived
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  exact chain _ _ (modify_preserves _ _ _ _ _ _) (fun _ => pure_preserves _)
private theorem traversal_preserves (origin : Nat) (pid : PeerId) : Preserves (traversal origin pid) := by
  unfold traversal
  simp only [branchCmp,Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  apply chain _ _ (lift_preserves (peer_read_frame pid))
  intro peer
  apply chain _ _ (lift_preserves (ambient_frame _))
  intro active
  split
  · exact chain _ _ (modify_preserves _ _ _ _ _ _) (fun _ => pure_preserves _)
  · exact pure_preserves _

private theorem capture_preserves (native : WG.M α) (frame : SameView queue native) :
    Preserves (captureWGRun native) :=
  StatePrefixPreserves.captureWGObserved (lift_preserves frame)

private theorem invariant_frame (why : String) : SameView queue (invariant why : WG.M α) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  change Except.error _ = Except.ok _ at run
  cases run

private theorem stats_frame (len : Nat) : SameView queue (modifyDev (rxStatsUpdate len)) :=
  of_workQueueFrame (Queues.WorkQueueFrames.update _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))

private theorem authenticatedSent_frame (pid : PeerId) : SameView queue (timersAnyAuthenticatedPacketSent pid) :=
  timer_delete_frame pid .sendKeepalive
private theorem authenticatedReceived_frame (pid : PeerId) : SameView queue (timersAnyAuthenticatedPacketReceived pid) :=
  timer_delete_frame pid .newHandshake

private theorem and_frame (a b : WG.M Bool) (ha : SameView queue a) (hb : SameView queue b) :
    SameView queue (WG.andM a b) := by
  unfold WG.andM
  apply SameView.bind ha
  intro yes
  split
  · exact hb
  · exact SameView.pure _ _
private theorem or_frame (a b : WG.M Bool) (ha : SameView queue a) (hb : SameView queue b) :
    SameView queue (WG.orM a b) := by
  unfold WG.orM
  apply SameView.bind ha
  intro yes
  split
  · exact SameView.pure _ _
  · exact hb

elab "receiver_inventory_choice" : tactic => do
  let target ← Lean.Meta.withReducible (Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget))
  unless target.isAppOf ``StatePrefixEnsures do Lean.throwError "expected prefix contract"
  let args := target.getAppArgs
  unless args[args.size - 2]!.isAppOf ``ite do Lean.throwError "expected choice"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply choice))

macro "receiver_native_frame" : tactic => `(tactic| first
  | with_reducible exact peer_read_frame _
  | with_reducible exact peer_write_frame _ _
  | with_reducible exact dev_read_frame
  | with_reducible exact peer_put_frame _
  | with_reducible exact session_frame _
  | with_reducible exact response_create_frame _
  | with_reducible exact mac_frame _ _
  | with_reducible exact send_frame _ _
  | with_reducible exact endpoint_frame _ _
  | with_reducible exact complete_frame _
  | with_reducible exact timer_delete_frame _ _
  | with_reducible exact authenticatedSent_frame _
  | with_reducible exact authenticatedReceived_frame _
  | with_reducible exact invariant_frame _
  | with_reducible exact stats_frame _
  | with_reducible exact cookie_consume_frame _
  | with_reducible exact cookie_send_frame _ _
  | with_reducible exact load_frame
  | with_reducible exact validate_frame _ _ _
  | with_reducible exact ambient_frame _
  | with_reducible apply and_frame
  | with_reducible apply or_frame
  | with_reducible apply SameView.bind
  | (session_origin_intro_forall; try dsimp only))

macro "receiver_inventory_step" : tactic => `(tactic| first
  | (with_reducible apply old_call; receiver_native_frame)
  | with_reducible exact old_initiation _
  | with_reducible exact old_response _
  | with_reducible exact call_preserves _ _ _ (fun _ => keepalive_preserves _ _)
  | with_reducible exact call_preserves _ _ _ (fun _ => derived_preserves _ _)
  | with_reducible exact call_preserves _ _ _ (fun _ => traversal_preserves _ _)
  | (with_reducible apply lift_preserves; receiver_native_frame)
  | with_reducible exact pure_preserves _
  | with_reducible apply chain
  | split
  | receiver_inventory_choice
  | receiver_native_frame
  | (session_origin_intro_forall; try dsimp only)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

theorem responseWith_preserves (mac : HandshakeMac) (pid : PeerId) :
    Preserves (responseWith (WorkRoot.ops mac) pid) := by
  unfold responseWith
  simp only [WorkRoot.ops,TimerRoot.ops,branch,hiddenClock64]
  repeat' receiver_inventory_step
  all_goals try simp_all only [Option.some.injEq]

elab "receiver_inventory_response" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``Preserves do Lean.throwError "expected preservation"
  unless target.getAppArgs.back!.isAppOf ``responseWith do Lean.throwError "expected response"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact responseWith_preserves _ _))

theorem afterMac_preserves (mac : HandshakeMac) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Preserves (afterMacWith (WorkRoot.ops mac) msg src loaded state) := by
  unfold afterMacWith
  simp only [WorkRoot.ops,TimerRoot.ops,branch,invariant]
  repeat' first | receiver_inventory_response | receiver_inventory_step
  all_goals try simp_all only [Option.some.injEq]

theorem receive_preserves (msg : Key) (src : SkbSource) : Preserves (WorkRoot.receive msg src) := by
  unfold WorkRoot.receive
  apply chain _ _ (lift_preserves (ambient_frame _))
  intro cookie
  split
  · exact chain _ _ (lift_preserves (cookie_consume_frame msg)) (fun _ => pure_preserves _)
  · apply chain _ _ (lift_preserves load_frame)
    intro loaded
    apply chain _ _ (capture_preserves _ (validate_frame msg src loaded))
    intro checked
    exact afterMac_preserves _ _ _ _ _

end Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
