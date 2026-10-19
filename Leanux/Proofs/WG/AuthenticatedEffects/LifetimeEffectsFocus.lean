import Leanux.Proofs.WG.AuthenticatedEffects.LifetimeEffectsReceipts
import Leanux.Proofs.WG.Queues.RemovalAppends

/-! Focusing the original lifetime helpers distributes through their exact
source using unconditional append facts, including stopped executions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.LifetimeEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

structure Ops.Appends (o : Ops (WGPrefix E)) : Prop where
  step : ∀ {α} (a : WG.M α), StateAppends (o.step a)
  peer : ∀ pid, StateAppends (o.peer pid)
  keypair : ∀ kid, StateAppends (o.keypair kid)
  modifyPeer : ∀ pid f, StateAppends (o.modifyPeer pid f)
  guard : ∀ pid, StateAppends (o.guard pid)
  arm : ∀ pid timer delay caller, StateAppends (o.arm pid timer delay caller)
  get : ∀ pid, StateAppends (o.get pid)
  put : ∀ pid, StateAppends (o.put pid)
  append : ∀ pid, StateAppends (o.append pid)

theorem native_appends : Ops.Appends native where
  step := StateAppends.lift
  peer := fun _ => StateAppends.focus _ _ _
  keypair := fun _ =>
    (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfigurationTail.«0».Leanux.Proofs.WG.Queues.RoutingJoint.readKey_appends) _
  modifyPeer := by
    intro pid f
    change StateAppends (modifyPeerKeysPrefix pid f)
    unfold modifyPeerKeysPrefix
    repeat' joint_append_step
  guard := by
    intro pid
    change StateAppends (modPeerTimerGuardPrefix pid)
    unfold modPeerTimerGuardPrefix
    repeat' joint_append_step
  arm := fun _ _ _ _ =>
    (pinned_const _private.Leanux.Proofs.WG.Queues.RemovalAppends.«0».Leanux.Proofs.WG.Queues.RoutingJoint.arm_appends) _ _ _ _
  get := fun _ => StateAppends.focus _ _ _
  put := fun _ => StateAppends.focus _ _ _
  append := fun _ => StateAppends.lift _

def Ops.focus (encode : E → F) (decode : F → Option E) (o : Ops (WGPrefix E)) : Ops (WGPrefix F) where
  step := fun a => focusStatePrefix encode decode (o.step a)
  peer := fun pid => focusStatePrefix encode decode (o.peer pid)
  keypair := fun kid => focusStatePrefix encode decode (o.keypair kid)
  modifyPeer := fun pid f => focusStatePrefix encode decode (o.modifyPeer pid f)
  guard := fun pid => focusStatePrefix encode decode (o.guard pid)
  arm := fun pid timer delay caller => focusStatePrefix encode decode (o.arm pid timer delay caller)
  get := fun pid => focusStatePrefix encode decode (o.get pid)
  put := fun pid => focusStatePrefix encode decode (o.put pid)
  append := fun pid => focusStatePrefix encode decode (o.append pid)

private def Aligned (encode : E → F) (decode : F → Option E)
    (g : WGPrefix F α) (t : WGPrefix E α) : Prop :=
  StateAppends t ∧ g = focusStatePrefix encode decode t

private theorem aligned_native (encode : E → F) (decode : F → Option E)
    (t : WGPrefix E α) (ht : StateAppends t) :
    Aligned encode decode (focusStatePrefix encode decode t) t := ⟨ht,rfl⟩

private theorem aligned_pure (encode : E → F) (decode : F → Option E) (x : α) :
    Aligned encode decode (pure x) (pure x) := by
  refine ⟨StateAppends.pure x,?_⟩
  funext w a h
  change (Except.ok (ε := Stop) ((x,w),a),h) = (Except.ok (ε := Stop) ((x,w),a),h ++ ((h.filterMap decode).drop (h.filterMap decode).length).map encode)
  simp

private theorem aligned_bind (encode : E → F) (decode : F → Option E)
    (inverse : ∀ e, decode (encode e) = some e)
    {g : WGPrefix F α} {t : WGPrefix E α} {f : α → WGPrefix F β} {b : α → WGPrefix E β}
    (hg : Aligned encode decode g t) (hf : ∀ x, Aligned encode decode (f x) (b x)) :
    Aligned encode decode (g >>= f) (t >>= b) := by
  refine ⟨hg.1.bind (fun x => (hf x).1),?_⟩
  rw [hg.2]
  have same : f = fun x => focusStatePrefix encode decode (b x) := funext (fun x => (hf x).2)
  rw [same]
  funext w a h
  exact focusPrefix_bind_appends encode decode inverse (hg.1 w)
    (fun out => (hf out.1).1 out.2) a h

private theorem aligned_choice (encode : E → F) (decode : F → Option E) (p : Prop) [Decidable p]
    {g k : WGPrefix F α} {t b : WGPrefix E α}
    (hg : p → Aligned encode decode g t) (hk : ¬p → Aligned encode decode k b) :
    Aligned encode decode (if p then g else k) (if p then t else b) := by
  by_cases hp : p <;> simp only [hp,↓reduceIte]
  · exact hg hp
  · exact hk hp


macro "lifetime_effects_align " enc:ident dec:ident inv:ident h:ident : tactic => `(tactic| first
  | with_reducible exact aligned_native $enc $dec _ (Ops.Appends.step $h _)
  | with_reducible exact aligned_native $enc $dec _ (Ops.Appends.peer $h _)
  | with_reducible exact aligned_native $enc $dec _ (Ops.Appends.keypair $h _)
  | with_reducible exact aligned_native $enc $dec _ (Ops.Appends.modifyPeer $h _ _)
  | with_reducible exact aligned_native $enc $dec _ (Ops.Appends.guard $h _)
  | with_reducible exact aligned_native $enc $dec _ (Ops.Appends.arm $h _ _ _ _)
  | with_reducible exact aligned_native $enc $dec _ (Ops.Appends.get $h _)
  | with_reducible exact aligned_native $enc $dec _ (Ops.Appends.put $h _)
  | with_reducible exact aligned_native $enc $dec _ (Ops.Appends.append $h _)
  | (maintenance_head Pure.pure; exact aligned_pure $enc $dec _)
  | (maintenance_head Bind.bind; apply aligned_bind $enc $dec $inv)
  | (maintenance_head ite; apply aligned_choice $enc $dec)
  | (maintenance_intro; try dsimp only)
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

variable (encode : E → F) (decode : F → Option E) (inverse : ∀ e, decode (encode e) = some e)
  (o : Ops (WGPrefix E)) (h : Ops.Appends o)
include inverse h

private theorem modify_aligned (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Aligned encode decode (modifyWith (Ops.focus encode decode o) site pid timer delay) (modifyWith o site pid timer delay) := by
  unfold modifyWith
  simp only [Ops.focus]
  repeat' first
    | lifetime_effects_align encode decode inverse h

theorem modify_focus (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    modifyWith (Ops.focus encode decode o) site pid timer delay =
      focusStatePrefix encode decode (modifyWith o site pid timer delay) :=
  (modify_aligned encode decode inverse o h site pid timer delay).2

private theorem traversal_aligned (pid : PeerId) :
    Aligned encode decode (traversalWith (Ops.focus encode decode o) pid) (traversalWith o pid) := by
  unfold traversalWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  simp only [Ops.focus]
  repeat' first
    | (maintenance_head modifyWith; exact modify_aligned encode decode inverse o h _ _ _ _)
    | lifetime_effects_align encode decode inverse h

theorem traversal_focus (pid : PeerId) :
    traversalWith (Ops.focus encode decode o) pid =
      focusStatePrefix encode decode (traversalWith o pid) :=
  (traversal_aligned encode decode inverse o h pid).2

private theorem dataSent_aligned (pid : PeerId) :
    Aligned encode decode (dataSentWith (Ops.focus encode decode o) pid) (dataSentWith o pid) := by
  unfold dataSentWith
  simp only [Ops.focus]
  repeat' first
    | lifetime_effects_align encode decode inverse h

theorem dataSent_focus (pid : PeerId) :
    dataSentWith (Ops.focus encode decode o) pid =
      focusStatePrefix encode decode (dataSentWith o pid) :=
  (dataSent_aligned encode decode inverse o h pid).2

private theorem queued_aligned (pid : PeerId) (retry : Bool) :
    Aligned encode decode (queuedWith (Ops.focus encode decode o) pid retry) (queuedWith o pid retry) := by
  unfold queuedWith
  simp only [Ops.focus]
  repeat' first
    | lifetime_effects_align encode decode inverse h

theorem queued_focus (pid : PeerId) (retry : Bool) :
    queuedWith (Ops.focus encode decode o) pid retry =
      focusStatePrefix encode decode (queuedWith o pid retry) :=
  (queued_aligned encode decode inverse o h pid retry).2

private theorem fresh_aligned (pid : PeerId) :
    Aligned encode decode (freshWith (Ops.focus encode decode o) pid) (freshWith o pid) := by
  unfold freshWith
  simp only [andPrefix,orPrefix]
  simp only [Ops.focus]
  repeat' first
    | (maintenance_head queuedWith; exact queued_aligned encode decode inverse o h _ _)
    | lifetime_effects_align encode decode inverse h

theorem fresh_focus (pid : PeerId) :
    freshWith (Ops.focus encode decode o) pid =
      focusStatePrefix encode decode (freshWith o pid) :=
  (fresh_aligned encode decode inverse o h pid).2

end Leanux.Proofs.WG.AuthenticatedEffects.LifetimeEffects
