import Leanux.Proofs.WG.AuthenticatedEffects.TimerSendFrames
import Leanux.Proofs.WG.AuthenticatedEffects.WorkRootAppends
import Leanux.Proofs.WG.AuthenticatedEffects.WorkRootClaims

/-! The complete native handshake receiver transports the actual timer-slot
carrier. Observed arms mint causes; deletion retires occurrences; other native
callbacks retain the incarnation, expiry and wheel-entry projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TimerInventory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes TimerRoot TimerSlots
open Origins.HandshakeSources
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

abbrev Inv (h : List Event) (w : WGWorld) (_ : Ambient) := TimerSlots.Carrier h w
abbrev Preserves (g : WGPrefix Event α) := StatePrefixPreserves Inv (fun _ => True) g

private theorem native_retained (action : WG.M α)
    (frame : ∀ initial, Framing.Preserves (TimerSlots.Retained initial) action) (h : List Event) :
    Framing.Preserves (TimerSlots.Carrier h) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact hi.retain ((hoare_iff_run_ambient _ _ _).mp (frame (view w)) w a result v b (retained_refl w) run)

private theorem native_delete (pid : PeerId) (t : PeerTimer) (h : List Event) :
    Framing.Preserves (TimerSlots.Carrier h) (delTimer pid t) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  exact hi.delete pid t w v a b run

private def completeTail (pid : PeerId) : WG.M Unit := do
  setPeer pid {(← getPeer pid) with timerHandshakeAttempts := 0,sentLastminuteHandshake := false}
  let now ← hidden .walltimeLastHandshake
  setPeer pid {(← getPeer pid) with walltimeLastHandshake := now}
private theorem complete_retained (pid : PeerId) (initial) :
    Framing.Preserves (TimerSlots.Retained initial) (completeTail pid) := by
  unfold completeTail
  simp only [hidden]
  repeat' timer_handshake_step initial
private theorem native_complete (pid : PeerId) (h : List Event) :
    Framing.Preserves (TimerSlots.Carrier h) (timersHandshakeComplete pid) := by
  change Framing.Preserves (TimerSlots.Carrier h) (delTimer pid .retransmitHandshake >>= fun _ => completeTail pid)
  exact preserves_bind (native_delete pid .retransmitHandshake h)
    (fun _ => native_retained _ (complete_retained pid) h)

private theorem native_sent (pid : PeerId) (h : List Event) :
    Framing.Preserves (TimerSlots.Carrier h) (timersAnyAuthenticatedPacketSent pid) :=
  native_delete pid .sendKeepalive h
private theorem native_received (pid : PeerId) (h : List Event) :
    Framing.Preserves (TimerSlots.Carrier h) (timersAnyAuthenticatedPacketReceived pid) :=
  native_delete pid .newHandshake h

private theorem framed {g : WGPrefix Event α} {native : WG.M α}
    (erases : ErasesStatePrefix g native) (appends : StateAppends g)
    (frame : ∀ h, Framing.Preserves (TimerSlots.Carrier h) native) : Preserves g := by
  intro w a h hi
  obtain ⟨suffix,history⟩ := appends w a h
  refine ⟨suffix,history,True.intro,?_⟩
  cases outcome : (runPrefix (g.run w) a h).1 with
  | error err => trivial
  | ok out =>
    rcases out with ⟨⟨result,v⟩,b⟩
    have nativeRun := (erases w a h).symm.trans outcome
    have output := (hoare_iff_run_ambient _ _ _).mp (frame h) w a result v b hi nativeRun
    exact history.symm ▸ output.append suffix

private theorem lift (native : WG.M α)
    (frame : ∀ h, Framing.Preserves (TimerSlots.Carrier h) native) : Preserves (liftWGPrefix native) :=
  framed (erasesStatePrefix_lift _) (StateAppends.lift _) frame
private theorem old_preserves (g : WGPrefix HandshakeCausal.Event α) (native : WG.M α)
    (erases : ErasesStatePrefix g native)
    (frame : ∀ h, Framing.Preserves (TimerSlots.Carrier h) native) : Preserves (old g) :=
  framed (focusStatePrefix_erases _ _ erases) (StateAppends.focus _ _ _) frame
private theorem old_call (kind : HandshakeCausal.Kind) (pid : PeerId) (native : WG.M α)
    (frame : ∀ h, Framing.Preserves (TimerSlots.Carrier h) native) :
    Preserves (old (HandshakeCausal.call kind pid native)) :=
  old_preserves _ _ (HandshakeCausal.call_erases _ _ _) frame
private theorem old_initiation (mac : HandshakeMac) : Preserves (old (HandshakeCausal.initiation mac)) :=
  old_preserves _ _ (HandshakeCausal.initiation_erases mac) (native_retained _ (consumeInitiation_retained mac.input))
private theorem old_response (mac : HandshakeMac) : Preserves (old (HandshakeCausal.response mac)) :=
  old_preserves _ _ (HandshakeCausal.response_erases mac) (native_retained _ (consumeResponse_retained mac.input))

private theorem pure_preserves (x : α) : Preserves (pure x) :=
  StatePrefixEnsures.pure x (fun _ _ _ _ => True.intro) (fun _ _ _ hi => hi)
private theorem chain (g : WGPrefix Event α) (next : α → WGPrefix Event β)
    (hg : Preserves g) (hf : ∀ x, Preserves (next x)) : Preserves (g >>= next) := StatePrefixEnsures.bind hg hf
private theorem choice (p : Prop) [Decidable p] (a b : WGPrefix Event α)
    (ha : Preserves a) (hb : Preserves b) : Preserves (if p then a else b) := by split <;> assumption
private theorem enter_preserves (kind : HandshakeCausal.Kind) (pid : PeerId) : Preserves (enter kind pid) :=
  fun _ _ _ hi => ⟨[.base (.callback kind pid)],rfl,True.intro,hi.append _⟩
private theorem call_preserves (kind : HandshakeCausal.Kind) (pid : PeerId)
    (body : Nat → WGPrefix Event α) (hb : ∀ origin, Preserves (body origin)) : Preserves (call kind pid body) :=
  StatePrefixEnsures.bind (enter_preserves kind pid) hb

private theorem keepalive_preserves (origin : Nat) (pid : PeerId) : Preserves (WorkRoot.keepalive origin pid) :=
  framed (WorkRoot.keepalive_erases origin pid) (WorkRoot.keepalive_appends origin pid)
    (native_retained _ (TimerSlots.keepalive_retained pid))
private theorem arm_preserves (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId)
    (t : PeerTimer) (delay : Nat) (caller : Option UInt64) : Preserves (arm origin kind pid t delay caller) :=
  TimerSlots.arm_preserves origin kind pid t delay caller
private theorem modify_preserves (origin : Nat) (kind : HandshakeCausal.Kind) (site : HiddenSite)
    (pid : PeerId) (t : PeerTimer) (delay : Nat) : Preserves (modifyTimer origin kind site pid t delay) := by
  unfold modifyTimer
  apply chain _ _ (lift _ (native_retained _ (fun initial => (callerJiffies_sameWGWorld site).wp (TimerSlots.Retained initial))))
  intro caller
  apply chain _ _ (lift _ (native_retained _ (guard_retained pid)))
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
  apply chain _ _ (lift _ (native_retained _ (fun initial => by repeat' timer_handshake_step initial)))
  intro peer
  apply chain _ _ (lift _ (native_retained _ (fun _ => hoare_liftAmbient _ _)))
  intro active
  split
  · exact chain _ _ (modify_preserves _ _ _ _ _ _) (fun _ => pure_preserves _)
  · exact pure_preserves _

macro "timer_receiver_native" : tactic => `(tactic| first
  | with_reducible exact native_complete _
  | with_reducible exact native_sent _
  | with_reducible exact native_received _
  | (with_reducible intro h; change Framing.Preserves (TimerSlots.Carrier h) (delTimer _ _); exact native_delete _ _ h)
  | ((with_reducible apply native_retained); intro initial
     repeat' first
       | (rx_retention_head beginSession; exact beginSession_retained _ initial)
       | (rx_retention_head createResponse; exact createResponse_retained _ initial)
       | (rx_retention_head addMacToPacket; exact addMac_retained _ _ initial)
       | (rx_retention_head sendBufferToPeer; exact sendBufferToPeer_retained _ _ initial)
       | (rx_retention_head setPeerEndpointFromSkb; exact endpoint_retained _ _ initial)
       | (rx_retention_head cookieMessageConsume; exact cookieConsume_retained _ initial)
       | (rx_retention_head sendHandshakeCookie; exact cookieSend_retained _ _ initial)
       | (rx_retention_head Cookies.loadPhase; exact retained_store Cookies.loadPhase_sameStore initial)
       | (rx_retention_head cookieValidatePacket; exact cookie_retained (cookieValidatePacket_sameCookie _ _ _) initial)
       | (rx_retention_head invariant; unfold invariant)
       | timer_handshake_step initial))

elab "timer_receiver_native_default" : tactic =>
  Lean.Meta.withTransparency .default do
    Lean.Elab.Tactic.evalTactic (← `(tactic| timer_receiver_native))

elab "timer_inventory_choice" : tactic => do
  let target ← Lean.Meta.withReducible (Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget))
  unless target.isAppOf ``StatePrefixEnsures do Lean.throwError "expected prefix contract"
  let args := target.getAppArgs
  unless args[args.size - 2]!.isAppOf ``ite do Lean.throwError "expected choice"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply choice))
macro "timer_inventory_step" : tactic => `(tactic| first
  | (with_reducible apply old_call; timer_receiver_native_default)
  | with_reducible exact old_initiation _
  | with_reducible exact old_response _
  | with_reducible exact call_preserves _ _ _ (fun _ => keepalive_preserves _ _)
  | with_reducible exact call_preserves _ _ _ (fun _ => derived_preserves _ _)
  | with_reducible exact call_preserves _ _ _ (fun _ => traversal_preserves _ _)
  | (with_reducible apply lift; timer_receiver_native_default)
  | with_reducible exact pure_preserves _
  | with_reducible apply chain
  | split
  | timer_inventory_choice
  | (session_origin_intro_forall; try dsimp only)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

theorem response_preserves (mac : HandshakeMac) (pid : PeerId) :
    Preserves (responseWith (WorkRoot.ops mac) pid) := by
  unfold responseWith
  simp only [WorkRoot.ops,TimerRoot.ops,branch,hiddenClock64]
  repeat' timer_inventory_step
  all_goals try simp_all only [Option.some.injEq]
elab "timer_inventory_response" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``Preserves do Lean.throwError "expected preservation"
  unless target.getAppArgs.back!.isAppOf ``responseWith do Lean.throwError "expected response"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact response_preserves _ _))

theorem afterMac_preserves (mac : HandshakeMac) (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Preserves (afterMacWith (WorkRoot.ops mac) msg src loaded state) := by
  unfold afterMacWith
  simp only [WorkRoot.ops,TimerRoot.ops,branch,invariant,WG.andM,WG.orM]
  repeat' first | timer_inventory_response | timer_inventory_step
  all_goals try simp_all only [Option.some.injEq]

theorem receive_preserves (msg : Key) (src : SkbSource) : Preserves (WorkRoot.receive msg src) := by
  unfold WorkRoot.receive
  simp only [branch]
  apply chain _ _ (lift _ (native_retained _ (fun _ => hoare_liftAmbient _ _)))
  intro cookie
  split
  · exact chain _ _ (lift _ (native_retained _ (cookieConsume_retained msg))) (fun _ => pure_preserves _)
  · apply chain _ _ (lift _ (native_retained _ (fun initial => retained_store Cookies.loadPhase_sameStore initial)))
    intro loaded
    apply chain _ _ (StatePrefixPreserves.captureWGObserved
      (lift _ (native_retained _ (fun initial => cookie_retained (cookieValidatePacket_sameCookie msg src loaded) initial))))
    intro checked
    exact afterMac_preserves _ _ _ _ _

end Leanux.Proofs.WG.AuthenticatedEffects.TimerInventory
