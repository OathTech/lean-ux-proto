import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumeLeafPointNative

/-! Endpoint guards and each adjacent peer metadata update remain in native order. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal


noncomputable def updateThenShape (pid : PeerId) (f : Peer → Peer)
    (fields : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged ∧ (f p).txQueue = p.txQueue)
    (next : WG.M α) (tail : Shape (wg next)) :
    Shape (wg (getPeer pid >>= fun p => setPeer pid (f p) >>= fun _ => next)) := by
  rw [← bind_assoc,wg_bind]
  exact .bind (.native (.base (.update pid f fields))) (fun _ => tail)

macro "consume_leaf_update" : tactic => `(tactic| (
  consume_leaf_wg_tail_head setPeer
  refine .native (.base (.update _ _ ?_))
  intro p
  exact ⟨rfl,rfl,rfl⟩))

elab "consume_leaf_set_prefix" : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source"
  unless action.isAppOf ``wg do Lean.throwError "not WG source"
  let some body := action.getAppArgs.back? | Lean.throwError "missing body"
  let body := body.consumeMData.headBeta
  unless body.isAppOf ``Bind.bind do Lean.throwError "not native bind"
  let args := body.getAppArgs
  let some head := args[args.size - 2]? | Lean.throwError "missing first read"
  unless head.consumeMData.headBeta.isAppOf ``getPeer do Lean.throwError "not peer read"
  let some tail := args.back? | Lean.throwError "missing tail"
  let .lam _ _ tail _ := tail.consumeMData | Lean.throwError "not continuation"
  let tail := tail.consumeMData.headBeta
  unless tail.isAppOf ``Bind.bind do Lean.throwError "not setter bind"
  let args := tail.getAppArgs
  let some write := args[args.size - 2]? | Lean.throwError "missing write"
  unless write.consumeMData.headBeta.isAppOf ``setPeer do Lean.throwError "not peer write"

macro "consume_leaf_update_then" : tactic => `(tactic| (
  consume_leaf_set_prefix
  apply updateThenShape
  · intro p; exact ⟨rfl,rfl,rfl⟩))

noncomputable def endpointEqShape (a : Endpoint) (b : Option Endpoint) :
    Shape (wg (endpointEq a b)) := by
  unfold endpointEq WG.andM
  repeat' consume_leaf_shape

noncomputable def cacheShape (pid : PeerId) : Shape (wg (dstCacheReset pid)) := by
  apply Shape.marked (.cache pid)
  unfold dstCacheReset
  repeat' first | consume_leaf_update | consume_leaf_update_then | consume_leaf_shape

noncomputable def endpointShape (pid : PeerId) (ep : Endpoint) : Shape (wg (setPeerEndpoint pid ep)) := by
  apply Shape.marked (.endpoint pid ep)
  unfold setPeerEndpoint requireNotPending
  repeat' first
    | consume_leaf_update
    | consume_leaf_update_then
    | (consume_leaf_wg_head endpointEq; exact endpointEqShape _ _)
    | (consume_leaf_wg_head dstCacheReset; exact cacheShape _)
    | consume_leaf_shape

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
