import Leanux.Proofs.WG.RetirementSecurity.RxSelectedCredit
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceTx
import Leanux.Proofs.WG.Queues.HolderAuxScheduler

/-! Exact key credit joins the existing scheduler's native accounting cut.
The TX worker derives physical separation and independent peer-release
protection before its real dequeue; its successor boundary is source-derived. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits
open DurableHolders

def Inv (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (temporary : Credits.Ledger) (locals : List TxLocalBatch) (active : List (List SkbId))
    (h : List RxHistory.Event) (w : World) : Prop :=
  HolderAuxiliary.Inv initial loans before h w ∧ HolderAccount temporary w.wg ∧
    OccurrenceStack.Ready locals active w.wg ∧ BaseCoherence.Inv w.wg ∧ KeySlotLiveness.Inv w.wg

theorem step_keys (pid : PeerId) : Hoare (liftWG (txStep pid))
    (Inv initial loans before temporary locals active h) (fun _ w=>HolderAccount temporary w.wg) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  obtain ⟨suffix,history,holders,funded,stable⟩ := entry.1.1.1
  have anchors := KeySlotLiveness.references entry.2.2.2.2 funded entry.2.2.2.1
    (HolderAuxiliary.owner_configured entry.1.2.1)
  have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
    _ w v result run
  exact entry.2.1.tx_step_holders entry.2.2.1.2.1 funded stable anchors pid w.ambient v.ambient native

theorem keys_product_store {action : Leanux.M α} (same : SameProductStore action) :
    Preserves (fun w : World=>HolderAccount temporary w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v keys run
  have fields := (ProjectedAction.iff_run _ _ _).mp same w result v run
  have dev : v.wg.dev=w.wg.dev := congrArg (fun p : ProductStore43=>p.2.2.2.dev) fields
  apply keys.points
  unfold ownershipPointView ownershipAt peerAt keyReferenceView keyAt packetKeyWords
  rw [dev]

theorem tx_keys (pid : PeerId) : Hoare (txIter pid (Env.condResched .txWorker))
    (Inv initial loans before temporary locals active h) (fun _ w=>HolderAccount temporary w.wg) := by
  unfold txIter workerIter
  apply hoare_bind _ _ (step_keys pid)
  intro more
  split
  · exact preserves_pure _
  · apply preserves_bind
    · apply preserves_bind (keys_product_store (condResched_sameKernel .txWorker))
      intro need
      exact productAmbient_spec (AmbientM.branch .txNeedResched need) _ (fun _ _ hi=>hi)
    · intro yielded
      split <;> exact preserves_pure _

/-- The complete actual TX iteration pays its detached key credit once and
re-establishes all independently derived incoming scheduler support. -/
theorem tx (pid : PeerId) : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe
    (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ := HolderAuxScheduler.tx_preserves initial loans before pid w h entry.1
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post
    have native := (RxHistory.mixed_erases (txIterPrefix_erases pid (erasesPrefix_lift _)) w h).symm.trans run
    have keys := (hoare_iff_run _ _ _).mp (tx_keys pid) w out.1 out.2 entry native
    have physical := (hoare_iff_run _ _ _).mp (OccurrenceTx.iteration pid) w out.1 out.2 entry.2.2.1 native
    have live := (hoare_iff_run _ _ _).mp (KeySlotLiveness.tx_iteration (pending:=[]) pid)
      w out.1 out.2 entry.2.2.2.2 native
    have structural := (ProjectedAction.iff_run _ _ _).mp
      (BaseCoherence.txIter_view pid (Env.condResched .txWorker) (BaseCoherence.product_store_view (condResched_sameKernel _)))
      w out.1 out.2 native
    exact ⟨post,keys,physical,BaseCoherence.transport entry.2.2.2.1 structural,live⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
