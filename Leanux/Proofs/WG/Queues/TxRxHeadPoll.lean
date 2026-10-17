import Leanux.Proofs.WG.Queues.TxRxHeadCompletion
import Leanux.Proofs.WG.Queues.CurrentSlotHistory

/-! The actual grouped RX poll, including arbitrary original product callbacks,
then the concrete Stack callback. No physical occupied-slot premise is used. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.RxHeadPoll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private abbrev Ready (target : SkbId) (state : PacketState) (w : WGWorld) : Prop :=
  Packets.Inv w ∧ HeadState target state w

private theorem peek_ready (pid target : Nat) (state : PacketState) :
    Preserves (Ready target state) (peekRxQueue pid) := by
  unfold peekRxQueue
  repeat' first
    | (allocation_release_head PrevQueue.peek
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.TxStackHead.«0».Leanux.Proofs.WG.Queues.TxDisposition.StackHead.store_ready)
         target state _ (prevQueuePeek_sameWGStore _))
    | rx_head_ready target, state

private theorem drop_ready (pid target : Nat) (state : PacketState) :
    Preserves (Ready target state) (dropRxQueue pid) := by
  unfold dropRxQueue
  repeat' rx_head_ready target, state

private theorem complete_ready (pid target : Nat) (state : PacketState) :
    Preserves (Ready target state) (completeRxQueue pid) := by
  unfold completeRxQueue
  repeat' rx_head_ready target, state

private theorem counter_ready (kid nonce target : Nat) (state : PacketState) :
    Preserves (Ready target state) (counterValidate kid nonce) := by
  unfold counterValidate WG.orM
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch,branchCmp,invariant]
  repeat' rx_head_ready target, state

theorem peek (pid target : Nat) (state : PacketState) :
    Preserves (StackHead.Inv target state) (peekRxQueue pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.TxRxHeadCompletion.«0».Leanux.Proofs.WG.Queues.TxDisposition.RxHeadCompletion.join_ready)
    target state (RxJoint.peekAccess pid) _ (RxJoint.peekAccess_erases pid)
    (RxJoint.peekAccess_allocation pid) (peek_ready pid target state)

theorem drop (pid target : Nat) (state : PacketState) :
    Preserves (StackHead.Inv target state) (dropRxQueue pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.TxRxHeadCompletion.«0».Leanux.Proofs.WG.Queues.TxDisposition.RxHeadCompletion.join_ready)
    target state (rxDropPeekedPrefix pid) _ (rxDropPeekedPrefix_erases pid)
    (rxDropPeekedPrefix_preserves allocationAmbient pid) (drop_ready pid target state)

theorem complete (pid target : Nat) (state : PacketState) :
    Preserves (StackHead.Inv target state) (completeRxQueue pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.TxRxHeadCompletion.«0».Leanux.Proofs.WG.Queues.TxDisposition.RxHeadCompletion.join_ready)
    target state (RxJoint.completeAccess pid) _ (RxJoint.completeAccess_erases pid)
    (RxJoint.completeAccess_allocation pid) (complete_ready pid target state)

theorem counter (kid nonce target : Nat) (state : PacketState) :
    Preserves (StackHead.Inv target state) (counterValidate kid nonce) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.TxRxHeadCompletion.«0».Leanux.Proofs.WG.Queues.TxDisposition.RxHeadCompletion.join_ready)
    target state (counterValidatePrefix kid nonce) _ (counterValidatePrefix_erases kid nonce)
    (AmbientContracts.drop (counterValidatePrefix_spec allocationAmbient (fun _=>True) kid nonce))
    (counter_ready kid nonce target state)

theorem getRx (id target : Nat) (state : PacketState) :
    Preserves (StackHead.Inv target state) (getRxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact (Packets.getRxSkb_current id w v result a b run).1 ▸ hi

theorem freeRx (id target : Nat) (state : PacketState) :
    Preserves (StackHead.Inv target state) (freeRxSkb id) := by
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.TxRxHeadLeaves.«0».Leanux.Proofs.WG.Queues.TxDisposition.RxHeadLeaves.join)
    target state (freeRxSkbPrefix id) _ (freeRxSkbPrefix_erases id) (allocationRx.free id)
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
      simpa only [HeadState,txPackets,Packets.update,hd,Option.bind_some,Option.map_some] using hi.2

/-- The original product callback remains arbitrary with its exact head and
allocation-state contract. All poll budgets and normal failure branches remain. -/
theorem poll (pid budget target : Nat) (state : PacketState)
    (callback : List (List UInt8)→Leanux.M Unit)
    (hc : ∀xs,Preserves (fun w:World=>StackHead.Inv target state w.wg) (callback xs)) :
    Preserves (fun w:World=>StackHead.Inv target state w.wg) (rxPoll pid budget callback) := by
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
       apply PublicationPoll.native_product (StackHead.Inv target state)
       simp only [monadLift_self]
       repeat' first
         | (rx_retention_head peekRxQueue; exact peek _ target state)
         | (rx_retention_head dropRxQueue; exact drop _ target state)
         | (rx_retention_head completeRxQueue; exact complete _ target state)
         | (rx_retention_head counterValidate; exact counter _ _ target state)
         | (rx_retention_head WG.consumeDataDone; exact RxHeadCompletion.consumeDataDone _ target state _ _)
         | (rx_retention_head getRxSkb; exact getRx _ target state)
         | (rx_retention_head freeRxSkb; exact freeRx _ target state)
         | (rx_retention_head WG.peerPut; exact RxHeadLeaves.peerPut _ target state)
         | (rx_retention_head keypairPut; exact RxHeadLeaves.keyPut _ _ target state)
         | (rx_retention_head endpointFromSkb
            exact (pinned_const _private.Leanux.Proofs.WG.Queues.TxStackHead.«0».Leanux.Proofs.WG.Queues.TxDisposition.StackHead.native_store)
              target state _ (endpointFromSkb_sameWGStore _))
         | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
         | rx_retention_step)
    | (allocation_release_lift_from AmbientM; exact productAmbient_spec _ _ (fun _ _ hi=>hi))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w:World=>StackHead.Inv target state w.wg)
       intro x b
       change Preserves (fun w:World=>StackHead.Inv target state w.wg) _)
    | rx_retention_step

theorem stack (pid budget target : Nat) (state : PacketState) :
    Preserves (fun w:World=>StackHead.Inv target state w.wg)
      (rxPoll pid budget (fun packets=>packets.forM Env.deliverInner)) :=
  poll pid budget target state _ (StackHead.stack_preserves target state)

end Leanux.Proofs.WG.Queues.TxDisposition.RxHeadPoll
