import Leanux.Proofs.WG.Queues.TxLiveRxCompletion
import Leanux.Proofs.WG.Queues.TxRxHeadPoll

/-! The original product RX poll retains the live logical encryption frontier.
Its delivery callback remains arbitrary until the concrete Stack corollary. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LivePoll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open LiveFrontier

private theorem peek (pid : Nat) :
    Preserves Ready (peekRxQueue pid) := by
  unfold peekRxQueue
  repeat' first
    | (allocation_release_head PrevQueue.peek
       exact store_ready _ (prevQueuePeek_sameWGStore _))
    | rx_live_step

private theorem drop (pid : Nat) :
    Preserves Ready (dropRxQueue pid) := by
  unfold dropRxQueue
  repeat' rx_live_step

private theorem complete (pid : Nat) :
    Preserves Ready (completeRxQueue pid) := by
  unfold completeRxQueue
  repeat' rx_live_step

private theorem counter (kid nonce : Nat) :
    Preserves Ready (counterValidate kid nonce) := by
  unfold counterValidate WG.orM
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch,branchCmp,invariant]
  repeat' rx_live_step

private theorem getRx (id : Nat) :
    Preserves Ready (getRxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact (Packets.getRxSkb_current id w v result a b run).1 ▸ hi

private theorem freeRx (id : Nat) :
    Preserves Ready (freeRxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  cases hd:w.dev with
  | none => simp [freeRxSkb,liftSkb_run,hd] at run
  | some d =>
    cases hp:d.rxSkbs[id]? with
    | none =>
      simp [freeRxSkb,liftSkb_run,SkbStore.freeRx,SkbStore.getRx,hd,hp,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      rw [Packets.freeRxSkb_run w a d id p hd hp] at run
      cases run
      simpa only [Ready,LiveFrontier.Inv,Physical,Packets.update,hd,Option.map_some,Option.some.injEq,forall_eq'] using hi

/-- The original product callback remains arbitrary with its live-ring frontier
and physical-refinement contract. All poll budgets and normal failure branches remain. -/
theorem poll (pid budget : Nat)
    (callback : List (List UInt8)→Leanux.M Unit)
    (hc : ∀xs,Preserves (fun w:World=>Ready w.wg) (callback xs)) :
    Preserves (fun w:World=>Ready w.wg) (rxPoll pid budget callback) := by
  rw [←rxPollGrouped_eq]
  unfold rxPollGrouped
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch,invariant,unsupported,WG.andM]
  repeat' first
    | (rx_retention_head napiGroReceive
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groReceive_preserves)
         _ callback hc _ _)
    | (rx_retention_head napiGroFlushAll
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groFlush_preserves)
         _ callback hc _)
    | (allocation_release_lift_from WG.M
       apply PublicationPoll.native_product Ready
       simp only [monadLift_self]
       repeat' first
         | (rx_retention_head peekRxQueue; exact peek _)
         | (rx_retention_head dropRxQueue; exact drop _)
         | (rx_retention_head completeRxQueue; exact complete _)
         | (rx_retention_head counterValidate; exact counter _ _)
         | (rx_retention_head WG.consumeDataDone; exact LiveRx.consume _ _ _)
         | (rx_retention_head getRxSkb; exact getRx _)
         | (rx_retention_head freeRxSkb; exact freeRx _)
         | (rx_retention_head WG.peerPut; exact LiveFrontier.peer_put _)
         | (rx_retention_head keypairPut; exact LiveFrontier.key_put _ _)
         | (rx_retention_head endpointFromSkb
            exact store_ready _ (endpointFromSkb_sameWGStore _))
         | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
         | rx_retention_step)
    | (allocation_release_lift_from AmbientM; exact productAmbient_spec _ _ (fun _ _ hi=>hi))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w:World=>Ready w.wg)
       intro x b
       change Preserves (fun w:World=>Ready w.wg) _)
    | rx_retention_step

theorem stack (pid budget : Nat) :
    Preserves (fun w:World=>Ready w.wg)
      (rxPoll pid budget (fun packets=>packets.forM Env.deliverInner)) :=
  poll pid budget _ LiveFrontier.stack


end Leanux.Proofs.WG.Queues.TxDisposition.LivePoll
