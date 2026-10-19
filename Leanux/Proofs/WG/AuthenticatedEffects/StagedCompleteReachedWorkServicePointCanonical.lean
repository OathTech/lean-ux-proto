import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkServicePointResidual

/-! Canonical work bookkeeping and key-maintenance witnesses. Each observer
bind is the original bind; each cached setter is paired with its actual read. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal RetirementSecurity Queues.RxCredits

noncomputable def stateBindShape (body : WGPrefix Event α) (next : α → WGPrefix Event β)
    (head : Shape (liftWGObserver body)) (tail : ∀ value, Shape (liftWGObserver (next value))) :
    Shape (liftWGObserver (body >>= next)) := by
  rw [liftWGObserver_bind]
  exact .bind head tail

noncomputable def updateThenShape (pid : PeerId) (f : Peer → Peer)
    (next : Unit → WGPrefix Event α)
    (fields : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged ∧ (f p).txQueue = p.txQueue)
    (tail : ∀ value, Shape (liftWGObserver (next value))) :
    Shape (liftWGObserver (liftWGPrefix (getPeer pid) >>= fun p => liftWGPrefix (setPeer pid (f p)) >>= next)) := by
  rw [← bind_assoc,← Queued.lift_bind,liftWGObserver_bind]
  exact .bind (.leaf (.native (.base (.update pid f fields)))) tail

theorem append_factor (pid : PeerId) :
    liftWGObserver (effects.append pid) = (do
      let h ← Consume.Leaf.historyRead
      liftWGObserver (TimerEffects.queueReceipt Event.queued (CausalScope.current scope? h) pid)) := by
  funext w h
  rfl

noncomputable def appendShape (pid : PeerId) : Shape (liftWGObserver (effects.append pid)) := by
  rw [append_factor]
  refine .bind (.leaf (.native .history)) ?_
  intro h
  unfold TimerEffects.queueReceipt
  rw [Consume.Points.wg_receipt_factor]
  refine .bind (.leaf (.native (.base (.basic .world)))) fun before => ?_
  refine .bind (.native (.change (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}) ?_)) fun value => ?_
  · intro w
    unfold StagedEntry.view Packets.epoch Staged.stagedAt PacketMaterial.view
      Packets.snapshot Packets.deviceStore TxDisposition.txPackets txQueueContents handoffTxView
    cases w.dev <;> rfl
  · exact .bind (.leaf (.native (.base (.basic .world)))) fun after =>
      .bind (.native (.queued ⟨CausalScope.current scope? h,pid,
        ⟨value,before.wg,after.wg,before.ambient,after.ambient⟩⟩)) (fun _ => .pure value)

noncomputable def handshakeClearLeaf (pid : PeerId) : Consume.Leaf.Shape (Consume.Leaf.wg (handshakeClear pid)) := by
  unfold handshakeClear handshakeZero
  repeat' first
    | consume_leaf_update
    | consume_leaf_update_then
    | (consume_leaf_wg_head IndexOwner.peerDeref; exact .native (.base (.dereference _)))
    | (consume_leaf_wg_head liftM; exact .native (.base (.unhash _)))
    | consume_leaf_shape

noncomputable def keysClearLeaf (pid : PeerId) : Consume.Leaf.Shape (Consume.Leaf.wg (keypairsClear pid)) := by
  let update : (Peer → Peer) → WG.M Unit := fun f => do setPeer pid (f (← getPeer pid))
  change Consume.Leaf.Shape (Consume.Leaf.wg (do
    let old := (← getPeer pid).keypairNext
    update (fun p => {p with keypairNext := none})
    keypairPut old true
    let old := (← getPeer pid).keypairPrevious
    update (fun p => {p with keypairPrevious := none})
    keypairPut old true
    let old := (← getPeer pid).keypairCurrent
    update (fun p => {p with keypairCurrent := none})
    keypairPut old true))
  dsimp only [update]
  repeat' first
    | consume_leaf_update
    | consume_leaf_update_then
    | (consume_leaf_wg_head keypairPut; exact Consume.Leaf.keyReleaseShape _ _)
    | consume_leaf_shape

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
