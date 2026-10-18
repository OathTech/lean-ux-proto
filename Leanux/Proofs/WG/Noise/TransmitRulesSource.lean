import Leanux.Proofs.WG.Noise.SlotFrames
import Leanux.Proofs.WG.AllowedIps.RoutingTxFrames
import Leanux.Proofs.WG.Queues.TxRxProtection

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.TransmitRules
open Leanux Leanux.WG Queues Lifetimes Leanux.Proofs.Framing Std.Do

theorem disposal_preserves (P : WGWorld → Prop) (pid : PeerId) (item : List SkbId) (kid : KeypairId)
    (free : ∀ id, Preserves P (freeTxSkb id))
    (key : Preserves P (keypairPut (some kid) false))
    (peer : Preserves P (peerPut (some pid))) :
    Preserves P (TxDisposition.disposeSource pid item kid) := by
  have loop : Preserves P (forIn item () (fun id _ => do
      freeTxSkb id; pure (ForInStep.yield ())) : WG.M Unit) :=
    list_view_spec id P item () _ (fun id _ =>
      preserves_bind (free id) (fun _ => preserves_pure _))
  exact preserves_bind loop (fun _ => preserves_bind key
    (fun _ => preserves_bind peer (fun _ => preserves_pure true)))

theorem body_preserves (P : WGWorld → Prop) (pid : PeerId) (selected : Option (List SkbId))
    (drop : Preserves P (do
      setPeer pid {(← getPeer pid) with txQueue := (← getPeer pid).txQueue.dropPeeked}))
    (completion : ∀ item, Preserves P (createDataDone pid item))
    (disposal : ∀ item kid, Preserves P (TxDisposition.disposeSource pid item kid))
    (packet : ∀ id, Preserves P (getTxSkb id)) :
    Preserves P (TxDisposition.bodySource pid selected) := by
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  routing_tx_source [TxDisposition.bodySource] using [drop,completion,disposal,packet,ambient]

/-- The actual TX step with its exact source mutations and callbacks. -/

theorem step_preserves (P : WGWorld → Prop) (pid : PeerId)
    (queue : ∀ f : PrevQueue (List SkbId) → PrevQueue (List SkbId),
      Preserves P (modifyPeer pid (fun p => {p with txQueue:=f p.txQueue})))
    (completion : ∀ item, Preserves P (createDataDone pid item))
    (key : ∀ kid now, Preserves P (keypairPut kid now))
    (peer : Preserves P (peerPut (some pid)))
    (packet : ∀ {α : Type} (a : SkbM α), Preserves P (liftSkb a))
    (peek : ∀ q : PrevQueue (List SkbId), Preserves P q.peek) :
    Preserves P (txStep pid) := by
  have read : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b pre run
    exact (getPeer_normal pid w v p a b run).1 ▸ pre
  have drop : Preserves P (do
      setPeer pid {(← getPeer pid) with txQueue := (← getPeer pid).txQueue.dropPeeked}) := by
    simpa only [Queues.RxCredits.modifyPeer_source,getPeer_twice] using queue PrevQueue.dropPeeked
  have body (selected : Option (List SkbId)) : Preserves P (TxDisposition.bodySource pid selected) :=
    body_preserves P pid selected drop completion
      (fun item kid => disposal_preserves P pid item kid (fun id => packet (SkbStore.freeTx id))
        (key (some kid) false) peer)
      (fun id => packet (SkbStore.getTx id))
  rw [← TxDisposition.stepSource_eq]
  unfold TxDisposition.stepSource
  simp only [bind_assoc]
  apply preserves_bind read
  intro p
  apply preserves_bind (peek p.txQueue)
  rintro ⟨selected,q⟩
  simpa only [Queues.RxCredits.modifyPeer_source,bind_assoc] using preserves_bind (queue (fun _=>q)) (fun _=>body selected)

end Leanux.Proofs.WG.Noise.TransmitRules
