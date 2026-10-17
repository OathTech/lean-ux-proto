import Leanux.Proofs.WG.Queues.RxTransmitPoll
import Leanux.Proofs.WG.Lifetimes.TxCallFocus

/-! The actual globally observed poll, with one local TX receipt stream.
The seed is the original incoming lifetime projection; promotion appends only
the actual new local suffix and retains every prior outer event. -/
namespace Leanux.Proofs.WG.Queues.RxTransmit
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes AllowedIps Packets

private theorem focus_ite {E F α : Type} (encode : E → F) (decode : F → Option E)
    (p : Prop) [Decidable p] (g h : PrefixM F α) (a b : PrefixM E α)
    (yes : p → Appends a ∧ g = focusPrefix encode decode a)
    (no : ¬p → Appends b ∧ h = focusPrefix encode decode b) :
    Appends (if p then a else b) ∧
      (if p then g else h) = focusPrefix encode decode (if p then a else b) := by
  by_cases hp : p
  · simpa only [ite_eq_left hp] using yes hp
  · simpa only [ite_eq_right hp] using no hp

private theorem focus_failure {E F α β : Type} (encode : E → F) (decode : F → Option E)
    (a : Leanux.M α) (failure : ∀ w, ∃ stop, a.run w = .error stop)
    (f : α → PrefixM F β) (g : α → PrefixM E β) :
    Appends (liftPrefix a >>= g) ∧
      (liftPrefix a >>= f) = focusPrefix encode decode (liftPrefix a >>= g) := by
  constructor
  · intro w h
    obtain ⟨stop,run⟩ := failure w
    exact ⟨[], by simp only [runPrefix_bind,runPrefix_lift,run,List.append_nil]⟩
  · funext w h
    obtain ⟨stop,run⟩ := failure w
    change runPrefix (liftPrefix a >>= f) w h =
      ((runPrefix (liftPrefix a >>= g) w (h.filterMap decode)).1,
       h ++ ((runPrefix (liftPrefix a >>= g) w (h.filterMap decode)).2.drop
         (h.filterMap decode).length).map encode)
    rw [runPrefix_bind,runPrefix_lift,run,runPrefix_bind,runPrefix_lift,run]
    simp only [List.drop_length,List.map_nil,List.append_nil]

/-- This guard selects only the actual lower source head. All selected
rules construct ordinary kernel-checked proof terms. -/
elab "stack_focus_head " wanted:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.Meta.whnf (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType))).consumeMData
  unless target.isAppOf ``And do Lean.throwError "not a focus conjunction"
  let parts := target.getAppArgs
  unless parts.size == 2 do Lean.throwError "invalid conjunction"
  let appends := parts[0]!.consumeMData
  unless appends.isAppOf ``Appends do Lean.throwError "not an append contract"
  let args := appends.getAppArgs
  unless args.size > 0 do Lean.throwError "missing source"
  let mut action := args.back!.consumeMData.headBeta
  let expected := wanted.getId.eraseMacroScopes.toString
  if action.isAppOf ``Bind.bind && expected != "Bind.bind" then
    let bindArgs := action.getAppArgs
    unless bindArgs.size ≥ 2 do Lean.throwError "missing bind operand"
    action := bindArgs[bindArgs.size - 2]!.consumeMData.headBeta
  if action.isAppOf ``liftPrefix && expected != "liftPrefix" then
    let liftArgs := action.getAppArgs
    unless liftArgs.size > 0 do Lean.throwError "missing lifted operand"
    action := liftArgs.back!.consumeMData.headBeta
  let actual ← match action.getAppFn with
    | .const n _ => pure n.toString
    | .fvar f => pure (← f.getDecl).userName.eraseMacroScopes.toString
    | _ => Lean.throwError "not a named source"
  unless actual == expected || actual.endsWith ("." ++ expected) do
    Lean.throwError "different source head"

/-- Focus distributes through the actual Stack reply source with an arbitrary
appending product transmit callback. -/
theorem reply4_focus {E F : Type} (encode : E → F) (decode : F → Option E)
    (inverse : ∀ e, decode (encode e) = some e)
    (xmit : Nat → Nat → List Packet → Nat → PrefixM E Int)
    (hx : ∀ family addr packets mtu, Appends (xmit family addr packets mtu))
    (dst : Nat) (bytes : List UInt8) :
    reply4With (fun f a p m => focusPrefix encode decode (xmit f a p m)) dst bytes =
      focusPrefix encode decode (reply4With xmit dst bytes) := by
  suffices checked : Appends (reply4With xmit dst bytes) ∧
      reply4With (fun f a p m => focusPrefix encode decode (xmit f a p m)) dst bytes =
      focusPrefix encode decode (reply4With xmit dst bytes) from checked.2
  unfold reply4With
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | (stack_focus_head xmit; exact ⟨hx _ _ _ _, rfl⟩)
    | (stack_focus_head liftPrefix; exact (pinned_const _private.Leanux.Proofs.WG.Lifetimes.TxCallFocus.«0».Leanux.Proofs.WG.Lifetimes.productFocused_lift) encode decode _)
    | (stack_focus_head Pure.pure; exact (pinned_const _private.Leanux.Proofs.WG.Lifetimes.TxCallFocus.«0».Leanux.Proofs.WG.Lifetimes.productFocused_pure) encode decode _)
    | (stack_focus_head Bind.bind; apply (pinned_const _private.Leanux.Proofs.WG.Lifetimes.TxCallFocus.«0».Leanux.Proofs.WG.Lifetimes.productFocused_bind) encode decode inverse)
    | (stack_focus_head ite; apply focus_ite encode decode)
    | maintenance_intro
    | split
    | dsimp (config := {failIfUnchanged := true}) only

theorem receive4_focus {E F : Type} (encode : E → F) (decode : F → Option E)
    (inverse : ∀ e, decode (encode e) = some e)
    (reply : Nat → List UInt8 → PrefixM E Unit)
    (hr : ∀ dst bytes, Appends (reply dst bytes)) (pkt : List UInt8) :
    receive4With (fun dst bytes => focusPrefix encode decode (reply dst bytes)) pkt =
      focusPrefix encode decode (receive4With reply pkt) := by
  suffices checked : Appends (receive4With reply pkt) ∧
      receive4With (fun dst bytes => focusPrefix encode decode (reply dst bytes)) pkt =
      focusPrefix encode decode (receive4With reply pkt) from checked.2
  unfold receive4With
  repeat' first
    | (stack_focus_head excluded; exact focus_failure encode decode (Env.Stack.excluded _) (stackExcluded_failure _) _ _)
    | (stack_focus_head invariant; exact focus_failure encode decode (invariant _) (fun _ => ⟨_,rfl⟩) _ _)
    | (stack_focus_head unsupported; exact focus_failure encode decode (unsupported _) (fun _ => ⟨_,rfl⟩) _ _)
    | (stack_focus_head reply; exact ⟨hr _ _, rfl⟩)
    | (stack_focus_head liftPrefix; exact (pinned_const _private.Leanux.Proofs.WG.Lifetimes.TxCallFocus.«0».Leanux.Proofs.WG.Lifetimes.productFocused_lift) encode decode _)
    | (stack_focus_head Pure.pure; exact (pinned_const _private.Leanux.Proofs.WG.Lifetimes.TxCallFocus.«0».Leanux.Proofs.WG.Lifetimes.productFocused_pure) encode decode _)
    | (stack_focus_head Bind.bind; apply (pinned_const _private.Leanux.Proofs.WG.Lifetimes.TxCallFocus.«0».Leanux.Proofs.WG.Lifetimes.productFocused_bind) encode decode inverse)
    | (stack_focus_head ite; apply focus_ite encode decode)
    | maintenance_intro
    | split
    | dsimp (config := {failIfUnchanged := true}) only

theorem stack_focus {E F : Type} (encode : E → F) (decode : F → Option E)
    (receive4 : List UInt8 → PrefixM E Unit) (pkt : List UInt8) :
    stackReceiveWith (fun bytes => focusPrefix encode decode (receive4 bytes)) pkt =
      focusPrefix encode decode (stackReceiveWith receive4 pkt) := by
  unfold stackReceiveWith
  dsimp only
  split
  · rfl
  · split <;> (funext w h; exact FocusesUnder.lift (I := fun _ _ => True) _ w h True.intro)

private theorem original_xmit_appends (f a : Nat) (p : List Packet) (m : Nat) :
    Appends (liftWGObserver (wgXmitPrefix f a p m)) := by
  apply StateAppends.liftWGObserver
  rw [wgXmitPrefix_front_factor]
  apply StateAppends.bind (txFrontPrefix_appends f a p m)
  intro result
  cases result with
  | error err => exact StateAppends.pure err
  | ok pid => exact txTailPrefix_appends pid

private theorem stack_old_factor (bytes : List UInt8) :
    stackReceiveWith (receive4With (reply4With
      (fun f a p m => RxJoint.access (liftWGObserver (wgXmitPrefix f a p m))))) bytes =
    RxJoint.access (stackReceivePrefix bytes) := by
  change stackReceiveWith (receive4With (reply4With
    (fun f a p m => focusPrefix RxJoint.Event.access RxJoint.accessEvent
      (liftWGObserver (wgXmitPrefix f a p m))))) bytes = _
  rw [show reply4With (fun f a p m => focusPrefix RxJoint.Event.access RxJoint.accessEvent
      (liftWGObserver (wgXmitPrefix f a p m))) =
    (fun dst bytes => focusPrefix RxJoint.Event.access RxJoint.accessEvent
      (reply4With (fun f a p m => liftWGObserver (wgXmitPrefix f a p m)) dst bytes)) from
    funext fun dst => funext fun bytes => reply4_focus RxJoint.Event.access RxJoint.accessEvent (fun _ => rfl) _ original_xmit_appends dst bytes]
  rw [show receive4With (fun dst bytes => focusPrefix RxJoint.Event.access RxJoint.accessEvent
      (reply4With (fun f a p m => liftWGObserver (wgXmitPrefix f a p m)) dst bytes)) =
    (fun bytes => focusPrefix RxJoint.Event.access RxJoint.accessEvent
      (receive4With (reply4With (fun f a p m => liftWGObserver (wgXmitPrefix f a p m))) bytes)) from
    funext fun bytes => receive4_focus RxJoint.Event.access RxJoint.accessEvent (fun _ => rfl) _
      (reply4With_appends _ original_xmit_appends) bytes]
  rw [stack_focus]
  rfl

/-- The existing Stack source, with only its actual TX callback instrumented. -/
def localStack : List UInt8 → PrefixM LocalEvent Unit :=
  stackReceiveWith (receive4With (reply4With transmit))

theorem localStack_projects (bytes : List UInt8) :
    ProjectsPrefix oldRx id (localStack bytes) (RxJoint.access (stackReceivePrefix bytes)) := by
  rw [← stack_old_factor]
  exact stackReceiveWith_projects oldRx _ _
    (fun pkt => receive4With_projects oldRx _ _
      (fun dst data => reply4With_projects oldRx _ _ transmit_projects dst data) pkt) bytes

theorem localStack_appends (bytes : List UInt8) : Appends (localStack bytes) :=
  stackReceiveWith_appends _
    (receive4With_appends _ (reply4With_appends _ transmit_appends)) bytes

/-- The existing poll body and GRO source use the instrumented Stack callback.
Every old atom is focused exactly once on its original RX subjournal. -/
def localPoll (pid : PeerId) (budget : Nat) : PrefixM LocalEvent Nat :=
  RxJoint.PollSource.pollWith
    (fun {_} g => focusPrefix LocalEvent.old oldRx g)
    (RxJoint.GroSource.receiveWith LocalEvent.old localStack)
    (RxJoint.GroSource.flushAllWith LocalEvent.old localStack) pid budget

theorem localPoll_projects (pid : PeerId) (budget : Nat) :
    ProjectsPrefix oldRx id (localPoll pid budget) (RxJoint.poll pid budget) := by
  apply RxJoint.PollSource.focused_projects LocalEvent.old oldRx oldRx_old
  · intro g e
    rw [RxJoint.GroSource.receive_factor]
    exact RxJoint.GroSource.receive_projects oldRx LocalEvent.old id _ _
      oldRx_old localStack_projects g e
  · intro g
    rw [RxJoint.GroSource.flushAll_factor]
    exact RxJoint.GroSource.flushAll_projects oldRx LocalEvent.old id _ _
      oldRx_old localStack_projects g

theorem localPoll_appends (pid : PeerId) (budget : Nat) : Appends (localPoll pid budget) :=
  RxJoint.PollSource.poll_appends _ _ _ (fun _ _ => Appends.focus _ _ _)
    (RxJoint.GroSource.receive_appends LocalEvent.old localStack localStack_appends)
    (RxJoint.GroSource.flushAll_appends LocalEvent.old localStack localStack_appends) pid budget

/-- Use the original fresh seed and append only the actual new local suffix. -/
def observePoll (pid : PeerId) (budget : Nat) : PrefixM TransmitJoint.Event Nat :=
  RxHistory.ObserveSource.seededWith seed promote (localPoll pid budget)

theorem observePoll_rx (pid : PeerId) (budget : Nat) :
    ProjectsPrefix globalRx id (observePoll pid budget) (RxHistory.observePoll pid budget) :=
  RxHistory.ObserveSource.observePollWith_projects globalRx oldRx LocalEvent.old promote
    (localPoll pid budget) pid budget oldRx_old promote_rx
    (localPoll_appends pid budget) (localPoll_projects pid budget)

theorem observePoll_appends (pid : PeerId) (budget : Nat) : Appends (observePoll pid budget) :=
  RxHistory.ObserveSource.seeded_appends _ _ _

/-- Exact source result, product state and Stop for every incoming outer
history. The native poll still invokes the actual product Stack callback. -/
theorem observePoll_erases (pid : PeerId) (budget : Nat) :
    ErasesPrefix (observePoll pid budget)
      (rxPoll pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)) := by
  intro w h
  have projected := congrArg Prod.fst (observePoll_rx pid budget w h)
  have original := RxHistory.observePoll_erases pid budget w (h.filterMap globalRx)
  have same := projected.symm.trans original
  change (runPrefix (observePoll pid budget) w h).1.map (fun (x,v) => (x,v)) = _ at same
  cases hr : (runPrefix (observePoll pid budget) w h).1 <;> simpa only [hr,Except.map] using same

/-- Each captured front keeps the actual outer routing prefix, including
Stops and old incoming histories that already contain other event kinds. -/
theorem observePoll_preserves (initial : FlatTable × FlatTable) (pid : PeerId) (budget : Nat) :
    PrefixPreserves (TransmitJoint.Inv initial) (TransmitJoint.Safe initial) (observePoll pid budget) :=
  Position.observed_preserves initial pid budget

private theorem lower_seeded_factor (pid : PeerId) (budget : Nat) :
    RxHistory.ObserveSource.seededWith
      (fun h => RxJoint.seed (RxHistory.prior (h.filterMap RoutingJoint.rxEvent)))
      (fun e => RoutingJoint.Event.rx (RxHistory.promote e)) (RxJoint.poll pid budget) =
    RoutingJoint.rxAction (RxHistory.observePoll pid budget) := by
  funext w h
  change ((runPrefix (RxJoint.poll pid budget) w _).1,
    h ++ ((runPrefix (RxJoint.poll pid budget) w _).2.drop _).map _) =
    ((runPrefix (RxJoint.poll pid budget) w _).1,
      h ++ ((h.filterMap RoutingJoint.rxEvent ++
        ((runPrefix (RxJoint.poll pid budget) w _).2.drop _).map RxHistory.promote).drop
        (h.filterMap RoutingJoint.rxEvent).length).map RoutingJoint.Event.rx)
  simp only [List.drop_append_length,List.map_map,Function.comp_def]

/-- Strong old-sum projection retains non-RX routing events at their exact
incoming positions as well as every original RX constructor. -/
theorem observePoll_projects (pid : PeerId) (budget : Nat) :
    ProjectsPrefix TransmitJoint.oldEvent id (observePoll pid budget)
      (RoutingJoint.rxAction (RxHistory.observePoll pid budget)) := by
  rw [← lower_seeded_factor]
  apply RxHistory.ObserveSource.seeded_projects TransmitJoint.oldEvent oldRx id
  · intro h
    rw [seed_oldRx,List.filterMap_filterMap]
    rfl
  · intro e
    cases e <;> rfl
  · exact localPoll_appends pid budget
  · exact localPoll_projects pid budget

end Leanux.Proofs.WG.Queues.RxTransmit
