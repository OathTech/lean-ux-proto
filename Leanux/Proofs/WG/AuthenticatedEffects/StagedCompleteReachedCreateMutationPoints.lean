import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreateAtomCalls
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseMutation
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreateMutationSource

/-! Creation's silent packet-mark and queue-install cuts belong to the
original canonical call or the fixed original read/guard/preparation prefix.
The queue write consumes its unpublished alias before the queued receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateMutation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity RetirementSecurity CausalJournal
open AllocatedObligation CompleteCarrier CreatePoints CreatePhase CreateComposition
open HandshakeSecurity.StagedDisposal
set_option maxHeartbeats 600000

inductive Point (pid : PeerId) (items : List SkbId) (w : World) (h : List CausalJournal.Event) :
    World → List CausalJournal.Event → Prop where
  | marked {packetState : PacketState}
      (call : AtomCall (createShape pid items) w h (.mark skb packetState) u prior context)
      (device : u.wg.dev=some d) (resident : d.txSkbs[skb]?=some packet) :
      Point pid items w h (markedWorld u d skb packet packetState) (markedHistory u skb prior)
  | installed (head : items.head?=some first)
      (read : runPrefix (Admission.actualOps.access (getPeerMixed pid)) w h=(.ok (peer,u),readHistory))
      (guarded : runPrefix (Admission.actualOps.step (branch .createDataDead peer.isDead)) u readHistory=
        (.ok (false,q),readHistory))
      (prepared : runPrefix (queueBefore pid items) q readHistory=(.ok (some cached,v),middle))
      (device : v.wg.dev=some d)
      (written : runPrefix (queuePrefix pid cached items) v middle=(.ok ((),cut),middle)) :
      Point pid items w h cut middle

/-- The original pending batch reaches the queue write with its same ledger;
the history growth is derived from the actual read and preparation calls. -/
theorem install_pending
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (pending : CreateDisposal.PendingBatch h ledger items)
    (read : runPrefix (Admission.actualOps.access (getPeerMixed pid)) w h=(.ok (peer,u),readHistory))
    (guarded : runPrefix (Admission.actualOps.step (branch .createDataDead peer.isDead)) u readHistory=
      (.ok (false,q),readHistory))
    (prepared : runPrefix (queueBefore pid items) q readHistory=(.ok (some cached,v),middle)) :
    CreateDisposal.PendingBatch middle ledger items := by
  obtain ⟨atGuard,suffix,grown⟩:=access_account _ _ (Lifetimes.getPeerMixed_erases pid)
    (Queued.read pid) before read
  have atQueue:=admission_queue_entry before read guarded
  obtain ⟨_,_,more,extended⟩:=before_accounted atQueue prepared
  rw [extended,grown]
  exact (pending.append suffix).append more

/-- Every declared native mutation point has a live account on the original
creation ledger's lineage, even before its access or queued record is emitted. -/
theorem Point.live (point : Point pid items w h v last)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (pending : CreateDisposal.PendingBatch h ledger items) :
    Live ledger debts locals pid items last v.wg := by
  cases point with
  | marked call device resident=>
    exact (marked_phase device resident (call.entry (create_covers pending before))).1
  | installed head read guarded prepared _ written=>
    obtain ⟨account,⟨d,device,resident⟩,_⟩:=install_entry before read guarded prepared
    obtain ⟨kept,native,_⟩:=installed_phase device resident (.refl ledger)
      (install_pending before pending read guarded prepared) account
    rw [native] at written
    cases written
    exact kept

theorem Point.residual (point : Point pid items w h v last) :
    ∃remaining,runPrefix (CreatePoints.body pid items) w h=runPrefix remaining v last := by
  cases point with
  | marked call device resident=>
    exact ⟨_,call.resume (mark_source device resident)⟩
  | installed head read guarded prepared device written=>
    rw [queue_native device] at written
    cases written
    rename_i first readHistory peer u q cached atWrite d
    refine ⟨(do queueDue pid cached items; installedTail pid items first),?_⟩
    rw [install_residual head read guarded prepared,runPrefix_bind,runPrefix_bind,queue_source device]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateMutation
