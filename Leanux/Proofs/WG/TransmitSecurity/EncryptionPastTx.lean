import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastTxFrames

/-! The actual encrypted/dead TX completion and release paths preserve prior
encryption exclusion; socket sends and native reference payments stay in order. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Tx
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open TxDisposition Keys Socket Maintenance
set_option maxHeartbeats 600000

private theorem send_skb (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    Preserves (Ready past active) (sendSkbToPeer pid bytes ds) := by
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head send4; exact socket4 _ _ _ _ _)
    | (allocation_release_head send6; exact socket6 _ _ _ _ _)
    | encryption_past_tx_step

private theorem fresh (pid : PeerId) : Preserves (Ready past active) (keepKeyFresh pid) := by
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (allocation_release_head sendQueuedHandshakeInitiation; exact ready_frame (LiveFrontier.queued _ _) (EncryptionPast.queued _ _))
    | encryption_past_tx_step

private theorem complete (pid : PeerId) (item : List SkbId) :
    Preserves (Ready past active) (createDataDone pid item) := by
  have ambient {α : Type} (a : AmbientM α) : Preserves (Ready past active) (monadLift a : WG.M α) := hoare_liftAmbient a (Ready past active)
  have traversal := ready_frame (LiveFrontier.traversal pid) (EncryptionPast.traversal pid) (past := past) (active := active)
  have authenticated := ready_frame (LiveFrontier.authenticated_sent pid) (EncryptionPast.del_timer pid _) (past := past) (active := active)
  have send := send_skb (past := past) (active := active) pid
  have dataSent := ready_frame (LiveFrontier.data_sent pid) (EncryptionPast.data_sent pid) (past := past) (active := active)
  have fresh := fresh (past := past) (active := active) pid
  have read := get_tx (past := past) (active := active)
  routing_tx_source [createDataDone] using [traversal,authenticated,send,dataSent,fresh,read,ambient]

theorem tx_step (pid : PeerId) : Preserves (Ready past active) (txStep pid) := by
  rw [← TxDisposition.stepSource_eq]
  have ambient {α : Type} (a : AmbientM α) : Preserves (Ready past active) (monadLift a : WG.M α) := hoare_liftAmbient a (Ready past active)
  have complete := complete (past := past) (active := active) pid
  have key (kp : Option KeypairId) : Preserves (Ready past active) (keypairPut kp false) := ready_frame (LiveFrontier.key_put kp false) (key_put kp false)
  have put : Preserves (Ready past active) (peerPut (some pid)) := ready_frame (LiveFrontier.peer_put _) (peer_put _)
  have dispose (item : List SkbId) (kp : KeypairId) : Preserves (Ready past active) (TxDisposition.disposeSource pid item kp) := by
    routing_tx_source [TxDisposition.disposeSource] using [free_tx,key,put]
  have drop : Preserves (Ready past active) (do let p ← getPeer pid; setPeer pid {p with txQueue := p.txQueue.dropPeeked}) := by
    repeat' encryption_past_tx_step
  have body (first : Option (List SkbId)) : Preserves (Ready past active) (TxDisposition.bodySource pid first) := by
    unfold TxDisposition.bodySource
    simp only [getPeer_twice]
    apply preserves_bind
    · routing_tx_source [WG.andM] using [get_tx,ambient]
    · intro go
      cases go with
      | false => exact preserves_pure false
      | true =>
        simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
        cases first with
        | none => exact ambient (AmbientM.invariant "unreachable")
        | some item =>
          cases hh : item.head? with
          | none => simp only [hh]; exact ambient (AmbientM.invariant "an empty ring item")
          | some headId =>
            simp only [hh]
            apply preserves_bind (get_tx headId)
            intro head
            apply preserves_bind drop
            intro _
            routing_tx_source [] using [complete,dispose,ambient]
  unfold TxDisposition.stepSource
  apply preserves_bind (show Preserves (Ready past active) (getPeer pid) from by encryption_past_tx_step)
  intro p
  apply preserves_bind (ready_store (prevQueuePeek_sameWGStore p.txQueue))
  intro out
  rcases out with ⟨first,queue⟩
  apply preserves_bind (show Preserves (Ready past active) (do
    let p ← getPeer pid
    setPeer pid {p with txQueue := queue}) from by repeat' encryption_past_tx_step)
  intro _
  exact body first

theorem tx (pid : PeerId) : Preserves (fun w : World=>Ready past active w.wg)
    (txIter pid (Env.condResched .txWorker)) := by
  let P := fun w : World=>Ready past active w.wg
  have step : Preserves P (monadLift (txStep pid) : Leanux.M Bool) :=
    PublicationPoll.native_product (Ready past active) _ (tx_step pid)
  have need : Preserves P (Env.condResched .txWorker) := product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi=>hi)
  routing_tx_source [txIter,workerIter] using [step,need,ambient]


end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Tx
