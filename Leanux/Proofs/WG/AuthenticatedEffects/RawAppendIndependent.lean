import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendDriver

/-! The direct append source neither reads nor rewrites its incoming event
history. This proved writer law lets a local completion observer be embedded
among other sending families without losing their earlier append positions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
open Leanux Leanux.WG Leanux.Proofs.Logged

def Independent (body : PrefixT E State α) : Prop :=
  ∀ w history, runPrefix body w history =
    ((runPrefix body w []).1,history ++ (runPrefix body w []).2)

theorem Independent.pure (value : α) : Independent (pure value : PrefixT E State α) := by
  intro w history
  change (Except.ok (ε := Stop) (value,w),history) = (_,history ++ [])
  rw [List.append_nil]
  rfl

theorem Independent.lift (body : StateT State (Except Stop) α) : Independent (liftPrefix body : PrefixT E State α) := by
  intro w history
  change (body.run w,history) = (body.run w,history ++ [])
  rw [List.append_nil]

theorem Independent.emit (event : E) : Independent (emitPrefix event : PrefixT E State Unit) := by
  intro w history
  rfl

theorem Independent.bind {body : PrefixT E State α} {next : α → PrefixT E State β}
    (first : Independent body) (tail : ∀ value, Independent (next value)) : Independent (body >>= next) := by
  intro w history
  rw [runPrefix_bind,runPrefix_bind,first w history]
  cases run : runPrefix body w [] with
  | mk result events =>
    cases result with
    | error stop => rfl
    | ok result =>
      obtain ⟨value,v⟩ := result
      change runPrefix (next value) v (history ++ events) =
        ((runPrefix (next value) v events).1,history ++ (runPrefix (next value) v events).2)
      rw [tail value v (history ++ events),tail value v events,List.append_assoc]

theorem Independent.ite (p : Prop) [Decidable p] {yes no : PrefixT E State α}
    (hy : p → Independent yes) (hn : ¬p → Independent no) : Independent (if p then yes else no) := by
  by_cases h : p <;> simp only [h,↓reduceIte]
  · exact hy h
  · exact hn h

theorem Independent.capture {body : PrefixT E State α} (independent : Independent body) :
    Independent (captureObserved body) := by
  intro w history
  rw [runPrefix_captureObserved,runPrefix_captureObserved,independent w history]

theorem Independent.forIn (xs : List α) (initial : β)
    (body : α → β → PrefixT E State (ForInStep β)) (independent : ∀ value state, Independent (body value state)) :
    Independent (forIn xs initial body) := by
  induction xs generalizing initial with
  | nil => exact Independent.pure initial
  | cons value rest ih =>
    rw [List.forIn_cons]
    apply Independent.bind (independent value initial)
    intro step
    cases step with
    | done state => exact Independent.pure state
    | yield state => exact ih state

theorem socket_independent (args : ProtocolSocket.Args) : Independent (liftWGObserver (socket args)) := by
  intro w history
  change
    ((runWGPrefix (socket args) w.wg w.ambient history).1.map
      (fun ((value,g),a) => (value,{w with wg := g,ambient := a})),
      (runWGPrefix (socket args) w.wg w.ambient history).2) =
    ((runWGPrefix (socket args) w.wg w.ambient []).1.map
      (fun ((value,g),a) => (value,{w with wg := g,ambient := a})),
      history ++ (runWGPrefix (socket args) w.wg w.ambient []).2)
  rw [socket_run,socket_run]
  cases front : (args.beforeAppend.run w.wg).run w.ambient with
  | error stop => simp
  | ok result => obtain ⟨⟨result,u⟩,b⟩ := result; cases result <;> simp

open Lean Meta Elab Tactic in
elab "raw_independent_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Independent do throwError "not a raw history-independence contract"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing source action"
  let action := args.back!.consumeMData.headBeta
  let .const actual _ := action.getAppFn | throwError "not a constant-headed source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different source head"

theorem transport_independent (pid : PeerId) (packet : RunWitness DataPacket) :
    Independent (transport pid packet) := by
  unfold transport
  repeat' first
    | (raw_independent_head liftWGObserver; exact socket_independent _)
    | (raw_independent_head captureObserved; exact Independent.capture (Independent.lift _))
    | (raw_independent_head liftPrefix; exact Independent.lift _)
    | (raw_independent_head Pure.pure; exact Independent.pure _)
    | (raw_independent_head Bind.bind; apply Independent.bind)
    | (raw_independent_head ite; apply Independent.ite)
    | (maintenance_intro; try dsimp only)
    | maintenance_reduce
    | split

theorem completion_independent (pid : PeerId) : Independent (completion pid) := by
  unfold completion CompletionEffects.stepWith CompletionEffects.bodyWith CompletionEffects.completeWith
    Queues.TxDisposition.andObs
  simp only [completionOps]
  repeat' first
    | (raw_independent_head transport; exact transport_independent _ _)
    | (raw_independent_head captureObserved; exact Independent.capture (Independent.lift _))
    | (raw_independent_head liftPrefix; exact Independent.lift _)
    | (raw_independent_head Pure.pure; exact Independent.pure _)
    | (raw_independent_head Bind.bind; apply Independent.bind)
    | (raw_independent_head ite; apply Independent.ite)
    | (raw_independent_head ForIn.forIn; apply Independent.forIn)
    | (maintenance_intro; try dsimp only)
    | maintenance_reduce
    | split

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
