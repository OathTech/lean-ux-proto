import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointShape

/-! Canonical witnesses for the actual creation callback. The original
pre-installation mark, queue receipt, ring choices and refusal walk appear
in their fixed source order, including all error-producing leaf calls. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation HandshakeSecurity.StagedDisposal HandshakeSecurity.StagedConservation
open CausalJournal
set_option maxHeartbeats 600000

noncomputable def beforeShape (pid : PeerId) (items : List SkbId) : Shape (queueBefore pid items) := by
  apply Shape.marked (.before pid items)
  unfold queueBefore
  cases items.head? with
  | none=>exact .atom (.fault _ .empty)
  | some first=>
    apply Shape.bind (.atom (.mark first .uncrypted))
    intro _
    apply Shape.bind (.atom (.peer pid))
    intro peer
    apply Shape.bind (.atom (.branch .enqueuePeerQueueFull (peer.txQueue.count ≥ MAX_QUEUED_PACKETS)))
    intro full
    cases full <;> exact .pure _

noncomputable def installShape (pid : PeerId) (peer : Peer) (items : List SkbId) : Shape (queueInstall pid peer items) :=
  .marked (.install pid peer items) (.bind (.atom (.queue pid peer items)) (fun _=>.atom (.event (.queued pid items))))

noncomputable def afterShape (items : List SkbId) : Shape (queueAfter items) := by
  apply Shape.marked (.ring items)
  unfold queueAfter
  apply Shape.bind (.atom .device)
  intro d
  apply Shape.bind (.atom (.nextCpu d.encryptLastCpu))
  intro cpu
  apply Shape.bind (.atom (.lastCpu cpu))
  intro _
  apply Shape.bind (.atom (.branch .enqueueRingFull d.encryptQueue.full))
  intro full
  cases full <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · exact .bind (.atom .queueEncrypt) (fun _=>.bind (.atom (.ring items)) (fun _=>.pure _))
  · exact .pure _

noncomputable def offeredShape (items : List SkbId) (ret : Int) : Shape (offered items ret) := by
  unfold offered
  split
  · exact .bind (.atom (.event (.ring (.offered items true)))) (fun _=>.pure _)
  · split
    · exact .bind (.atom (.event (.ring (.offered items false)))) (fun _=>.pure _)
    · exact .pure _

noncomputable def enqueueShape (pid : PeerId) (items : List SkbId) : Shape (Admission.actualOps.enqueue pid items) := by
  apply Shape.marked (.enqueue pid items)
  rw [enqueue_factor]
  unfold enqueue
  apply Shape.bind
  · apply Shape.bind (beforeShape pid items)
    intro candidate
    cases candidate with
    | none=>exact .pure _
    | some peer=>exact .bind (installShape pid peer items) (fun _=>afterShape items)
  · exact offeredShape items

noncomputable def borrowShape (items : List SkbId) : Shape (Publication.borrow items) := by
  apply Shape.marked (.borrow items)
  unfold Publication.borrow
  cases items.head? with
  | none=>exact .atom (.fault _ .empty)
  | some first=>exact .bind (.atom (.packet first)) (fun packet=>
      .bind (.atom (.owner packet.keypair)) (fun owner=>
        .bind (.atom (.acquire owner)) (fun _=>.pure _)))

noncomputable def markShape (pid : PeerId) (first : SkbId) (state : PacketState) :
    Shape (publicationMark pid first state) := by
  apply Shape.marked (.published pid first state)
  unfold publicationMark
  apply Shape.bind (.atom (.peer pid))
  intro peer
  split
  · exact .bind (.atom (.fault Unit .unqueued)) (fun _=>
      .bind (.atom (.mark first state)) (fun _=>.atom (.event (.published pid first state))))
  · exact .bind (.atom (.mark first state)) (fun _=>.atom (.event (.published pid first state)))

noncomputable def scheduleShape (pid : PeerId) : Shape (publicationSchedule pid) := by
  apply Shape.marked (.schedule pid)
  unfold publicationSchedule
  apply Shape.bind (.atom (.chooseCpu pid))
  intro _
  apply Shape.bind (.atom .device)
  intro d
  apply Shape.bind (.atom (.peekWork pid))
  intro queued
  split
  · exact .bind (.atom (.recordWork pid)) (fun _=>.atom (.appendWork pid))
  · exact .pure _

noncomputable def publishedShape (items : List SkbId) (state : PacketState) : Shape (publishedPrefix items state) :=
  .bind (borrowShape items) (fun (first,pid)=>.bind (markShape pid first state) (fun _=>.pure _))

noncomputable def publishShape (items : List SkbId) (state : PacketState) :
    Shape (TxSource.publish Admission.actualOps items state) := by
  apply Shape.marked (.publication items state)
  rw [published_prefix_factor]
  exact .bind (publishedShape items state) (fun (_,pid)=>
    .bind (scheduleShape pid) (fun _=>.child (.release (some pid))))

noncomputable def frontShape (pid : PeerId) (items : List SkbId) : Shape (Admission.actual pid items) := by
  apply Shape.marked (.admission pid items)
  unfold Admission.actual Admission.front
  apply Shape.bind (.atom (.peer pid))
  intro peer
  apply Shape.bind (.atom (.branch .createDataDead peer.isDead))
  intro dead
  cases dead <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · apply Shape.bind (enqueueShape pid items)
    intro ret
    apply Shape.bind (.atom (.branch .createDataEpipe (ret == -WG.EPIPE)))
    intro pipe
    cases pipe <;> first
      | exact .bind (.pure ()) (fun _=>.pure _)
      | exact .bind (publishShape items .dead) (fun _=>.pure _)
  · exact .pure _

noncomputable def freeShape (reason : Terminal.Reason) (items : List SkbId) :
    Shape (CreateDisposal.loop reason items) := by
  induction items with
  | nil=>exact .pure ()
  | cons id items ih=>
    rw [CreateDisposal.loop_cons]
    exact .bind (.child (.free reason id)) (fun _=>ih)

noncomputable def tailShape (pid : PeerId) (items : List SkbId) (first : SkbId) (ret : Int) :
    Shape (Admission.tail Admission.actualOps CreateDisposal.free pid items first ret) := by
  apply Shape.marked (.tail pid items first ret)
  unfold Admission.tail
  apply Shape.bind (.atom (.branch .createDataOk (ret == 0)))
  intro ok
  cases ok <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · apply Shape.bind (.atom (.branch .createDataOkEpipe (ret == -WG.EPIPE)))
    intro pipe
    cases pipe <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact .bind (.atom (.packet first)) (fun packet=>
        .bind (.child (.repay (some packet.keypair))) (fun _=>
          .bind (.child (.release (some pid))) (fun _=>freeShape (.createRefused pid ret) items)))
    · exact .pure _
  · exact .pure _

noncomputable def createShape (pid : PeerId) (items : List SkbId) : Shape (body pid items) := by
  apply Shape.marked (.create pid items)
  unfold body
  rw [Admission.final_factor]
  cases items.head? with
  | none=>exact .atom (.fault _ .empty)
  | some first=>exact .bind (frontShape pid items) (tailShape pid items first)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
