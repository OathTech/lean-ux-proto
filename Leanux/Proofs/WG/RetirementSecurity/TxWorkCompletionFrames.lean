import Leanux.Proofs.WG.RetirementSecurity.TxWorkSocketFrames
import Leanux.Proofs.WG.RetirementSecurity.TxDispositionCoverage

/-! Actual TX completion and disposal retain the pending TX actor queue.
The actor being executed is represented separately by its scheduler caller. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem sendQueued_work (pid : PeerId) (retry : Bool) :
    SameView queued (sendQueuedHandshakeInitiation pid retry) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' first
    | (rx_retention_head branchExpired
       exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => queued w = initial))
    | (rx_retention_head peerGet; exact (peer_get _).wp (fun s => s = initial))
    | (rx_retention_head peerPut; exact (peer_put _).wp (fun s => s = initial))
    | tx_work_step initial

theorem keepKeyFresh_work (pid : PeerId) : SameView queued (keepKeyFresh pid) := by
  intro initial
  exact RxCredits.TxReservation.keepKeyFresh_preserves _ pid
    ((sendQueued_work pid false).wp (fun s => s = initial))

theorem createDataDone_work (pid : PeerId) (items : List SkbId) :
    SameView queued (createDataDone pid items) := by
  intro initial
  change Preserves (fun w => queued w = initial) _
  unfold createDataDone timersAnyAuthenticatedPacketSent WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => queued w = initial)
       intro x b
       change Preserves (fun w => queued w = initial) _)
    | (rx_retention_head timersTraversal
       exact (timersTraversal_work _).wp (fun s => s = initial))
    | (rx_retention_head delTimer
       exact (delTimer_work _ _).wp (fun s => s = initial))
    | (rx_retention_head sendSkbToPeer
       exact (sendSkbToPeer_work _ _ _).wp (fun s => s = initial))
    | (rx_retention_head timersDataSent
       exact (timersDataSent_work _).wp (fun s => s = initial))
    | (rx_retention_head keepKeyFresh
       exact (keepKeyFresh_work _).wp (fun s => s = initial))
    | tx_work_step initial


theorem step_work (pid : PeerId) : SameView queued (txStep pid) := by
  intro initial
  let P := fun w=>queued w=initial
  have read (peer : PeerId) : Preserves P (getPeer peer) := getPeer_preserves _ _
  have write (peer : PeerId) (value : Peer) : Preserves P (setPeer peer value) := by
    unfold setPeer
    apply (modify _ ?_).wp (·=initial)
    intro d; rfl
  have packet (id : SkbId) : Preserves P (getTxSkb id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a value v b before run
    exact (Packets.getTxSkb_current id w v value a b run).1 ▸ before
  have free (id : SkbId) : Preserves P (freeTxSkb id) := by
    unfold freeTxSkb
    apply hoare_liftSkb
    intro w d store before device
    simpa only [P,queued,device,Option.map_some,Option.getD_some] using before
  have key (kid : Option KeypairId) (now : Bool) : Preserves P (keypairPut kid now) :=
    (key_put kid now).wp (·=initial)
  have peer (owner : Option PeerId) : Preserves P (peerPut owner) :=
    (peer_put owner).wp (·=initial)
  have complete (owner : PeerId) (items : List SkbId) : Preserves P (createDataDone owner items) :=
    (createDataDone_work owner items).wp (·=initial)
  have peek (queue : PrevQueue (List SkbId)) : Preserves P queue.peek :=
    (store (prevQueuePeek_sameWGStore queue)).wp (·=initial)
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : WG.M α) :=
    hoare_liftAmbient action P
  change Preserves P _
  routing_tx_source [txStep] using [read,write,packet,free,key,peer,complete,peek,ambient]

end Leanux.Proofs.WG.RetirementSecurity.TxWork
