import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumePointCapture

/-! The original counter bitmap loop has only local accumulator updates until
its single native key setter. Every guard and failing bound check remains in
its original order. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

elab "consume_shape_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn
    | Lean.throwError "not a constant source head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different source head"

elab "consume_native_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  unless action.consumeMData.isAppOf ``liftPrefix do Lean.throwError "not a native lift"
  let some native := action.getAppArgs.back? | Lean.throwError "missing native action"
  let native := native.consumeMData
  let native ← if native.isAppOf ``liftWG then
      match native.getAppArgs.back? with
      | some action => pure action.consumeMData
      | none => Lean.throwError "missing WG action"
    else pure native
  let .const actual _ := native.getAppFn | Lean.throwError "not a native head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different native head"

elab "consume_failure_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source action"
  let action := action.consumeMData.headBeta
  unless action.isAppOf ``Bind.bind do Lean.throwError "not a source bind"
  let args := action.getAppArgs
  let some body := args[args.size - 2]? | Lean.throwError "missing body"
  unless body.isAppOf ``liftPrefix do Lean.throwError "not a native failure"
  let some native := body.getAppArgs.back? | Lean.throwError "missing native action"
  let .const actual _ := native.consumeMData.headBeta.getAppFn | Lean.throwError "not a native head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different failure head"

elab "consume_wg_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let action := action.consumeMData.headBeta
  let body ← if action.isAppOf ``wg then
      match action.getAppArgs.back? with
      | some body => pure body
      | none => Lean.throwError "missing WG body"
    else do
      unless action.isAppOf ``liftWGObserver do Lean.throwError "not a WG observer"
      let some observer := action.getAppArgs.back? | Lean.throwError "missing observer"
      unless observer.isAppOf ``liftWGPrefix do Lean.throwError "not a native lift"
      let some body := observer.getAppArgs.back? | Lean.throwError "missing body"
      pure body
  let .const actual _ := body.consumeMData.headBeta.getAppFn | Lean.throwError "not a native head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different native head"

elab "consume_wg_tail_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let action := action.consumeMData.headBeta
  let body ← if action.isAppOf ``wg then
      match action.getAppArgs.back? with
      | some body => pure body
      | none => Lean.throwError "missing native WG body"
    else do
      unless action.isAppOf ``liftWGObserver do Lean.throwError "not a WG observer"
      let some observer := action.getAppArgs.back? | Lean.throwError "missing observer"
      unless observer.isAppOf ``liftWGPrefix do Lean.throwError "not native WG"
      let some body := observer.getAppArgs.back? | Lean.throwError "missing body"
      pure body
  let body := body.consumeMData.headBeta
  unless body.isAppOf ``Bind.bind do Lean.throwError "not a native bind"
  let some tail := body.getAppArgs.back? | Lean.throwError "missing tail"
  let .lam _ _ tail _ := tail.consumeMData | Lean.throwError "not a lambda"
  let .const actual _ := tail.consumeMData.headBeta.getAppFn | Lean.throwError "not a tail head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different tail head"

elab "consume_wg_failure_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let action := action.consumeMData.headBeta
  unless action.isAppOf ``Bind.bind do Lean.throwError "not a bind"
  let args := action.getAppArgs
  let some observer := args[args.size - 2]? | Lean.throwError "missing body"
  let observer := observer.consumeMData.headBeta
  unless observer.isAppOf ``liftWGObserver do Lean.throwError "not a WG observer"
  let some body := observer.getAppArgs.back? | Lean.throwError "missing observer"
  unless body.isAppOf ``liftWGPrefix do Lean.throwError "not a native lift"
  let some native := body.getAppArgs.back? | Lean.throwError "missing native action"
  let .const actual _ := native.consumeMData.headBeta.getAppFn | Lean.throwError "not a native head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different native failure"


theorem wg_bind (body : WG.M α) (next : α → WG.M β) :
    wg (body >>= next) = (wg body >>= fun value => wg (next value)) := by
  simp only [wg,Queued.lift_bind,liftWGObserver_bind]

theorem wg_if (test : Prop) [Decidable test] (yes no : WG.M α) :
    wg (if test then yes else no) = (if test then wg yes else wg no) := by
  split <;> rfl

noncomputable def wgBindShape (body : WG.M α) (next : α → WG.M β)
    (head : Shape (wg body)) (tail : ∀ value, Shape (wg (next value))) :
    Shape (liftWGObserver (liftWGPrefix (body >>= next))) := by
  change Shape (wg (body >>= next))
  rw [wg_bind]
  exact .bind head tail

noncomputable def wgIfShape (test : Prop) [Decidable test] (yes no : WG.M α)
    (left : test → Shape (wg yes)) (right : ¬test → Shape (wg no)) :
    Shape (liftWGObserver (liftWGPrefix (if test then yes else no))) := by
  change Shape (wg (if test then yes else no))
  rw [wg_if]
  exact conditionalShape test left right

noncomputable def wgListShape (xs : List α) (initial : σ)
    (body : α → σ → WG.M (ForInStep σ)) (shapes : ∀ item acc, Shape (wg (body item acc))) :
    Shape (wg (forIn xs initial body)) := by
  induction xs generalizing initial with
  | nil => exact .pure initial
  | cons item rest ih =>
    rw [List.forIn_cons,wg_bind]
    apply Shape.bind (shapes item initial)
    intro decision
    cases decision with
    | done final => exact .pure final
    | yield next => exact ih next

macro "consume_native_shape" : tactic => `(tactic| first
  | (consume_wg_failure_head invariant; exact .failed (.wgInvariant _) _)
  | (consume_wg_head branch; exact .native (.branch _ _))
  | (consume_wg_head branchCmp; exact .native (.compare _ _ _ _))
  | (consume_wg_head getKeypair; exact .native (.metadata _ (PeerMetadata.keyReadShape _)))
  | (consume_wg_head setKeypair; exact .native (.writeKey _ _))
  | (consume_wg_head getPeer; exact .native (.metadata _ (PeerMetadata.peerReadShape _)))
  | (consume_wg_head branchExpired; exact .native (.metadata _ (PeerMetadata.expiredShape _ _ _)))
  | (consume_wg_head invariant; exact .native (.wgInvariant _))
  | (consume_wg_head Pure.pure; exact .pure _)
  | (consume_wg_head Bind.bind; apply wgBindShape)
  | (consume_wg_head ite; apply wgIfShape)
  | (consume_wg_head ForIn.forIn; apply wgListShape)
  | (consume_shape_head Bind.bind; apply Shape.bind)
  | (consume_shape_head Pure.pure; exact .pure _)
  | (consume_shape_head ite; apply conditionalShape)
  | maintenance_intro
  | split
  | (simp +failIfUnchanged only))

noncomputable def counterShape (kid : KeypairId) (nonce : Nat) :
    Shape (wg (counterValidate kid nonce)) := by
  apply Shape.marked (.counter kid nonce)
  unfold counterValidate WG.orM
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' consume_native_shape

noncomputable def counterReceiptShape (skb : SkbId) (packet : RxPacket) :
    Shape (hooks.counterCheck skb packet) := by
  apply Shape.marked (.counterReceipt skb packet)
  rw [counter_factor]
  exact .bind (.native .world) (fun before =>
    .bind (counterShape packet.keypair packet.nonce) (fun value =>
      .bind (.native .world) (fun after =>
        .bind (.native (.replay skb packet ⟨value,before,after⟩)) (fun _ => .pure value))))

noncomputable def confirmationBodyShape (pid : PeerId) (kid : KeypairId) :
    Shape (wg (receivedWithKeypair pid kid)) := by
  unfold receivedWithKeypair
  rw [wg_bind]
  refine .bind (.native (.metadata _ (PeerMetadata.peerReadShape pid))) ?_
  intro first
  rw [wg_bind]
  refine .bind (.native (.branch .receivedNotNew (first.keypairNext != some kid))) ?_
  intro firstTest
  rw [wg_if]
  apply conditionalShape
  · intro stopped
    exact .pure false
  · intro passed
    rw [wg_bind]
    refine .bind (.native (.metadata _ (PeerMetadata.peerReadShape pid))) ?_
    intro second
    rw [wg_bind]
    refine .bind (.native (.branch .receivedChanged (second.keypairNext != some kid))) ?_
    intro secondTest
    rw [wg_if]
    apply conditionalShape
    · intro stopped
      exact .pure false
    · intro passed
      rw [wg_bind]
      refine .bind (.native (.metadata _ (PeerMetadata.peerReadShape pid))) ?_
      intro peer
      rw [wg_bind]
      refine .bind (.native (.metadata _ (PeerMetadata.previousShape pid))) ?_
      intro ignored
      rw [wg_bind]
      refine .bind (.child (.keyRelease peer.keypairPrevious)) ?_
      intro ignored
      rw [wg_bind]
      exact .bind (.native (.metadata _ (PeerMetadata.currentShape pid kid))) (fun _ => .pure true)

noncomputable def confirmationShape (pid : PeerId) (kid : KeypairId) :
    Shape (liftWGObserver (hooks.confirmation pid kid)) := by
  apply Shape.marked (.confirmation pid kid)
  rw [confirmation_factor]
  exact .bind (.native .world) (fun before =>
    .bind (confirmationBodyShape pid kid) (fun value =>
      .bind (.native .world) (fun after =>
        .bind (.native (.confirmed pid kid ⟨value,before.wg,after.wg,before.ambient,after.ambient⟩))
          (fun _ => .pure value))))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Points
