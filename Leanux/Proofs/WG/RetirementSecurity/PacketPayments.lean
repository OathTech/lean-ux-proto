import Leanux.Proofs.WG.RetirementSecurity.HolderFrames
import Leanux.Proofs.WG.Queues.TxDisposition
import Leanux.Proofs.WG.Queues.RxCleanupProtection

/-! The existing original TX disposal grouping frees every skb and pays
one key reference for the batch, followed by a separate peer reference.
Its parameter is the saved head's key at the original caller; transport of
that caller-owned loan is separate from this exact disposal contract. -/
namespace Leanux.Proofs.WG.RetirementSecurity.Credits
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem put_account (allocation : Allocation) (remaining : Ledger) (now : Bool) :
    Hoare (keypairPut (some allocation.slot) now) (Exact (allocation :: remaining))
      (fun _ => Exact remaining) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  exact hi.put now a b run

theorem freeTxList_preserves (items : List SkbId) (credits : Ledger) :
    Preserves (Exact credits) (forIn items () fun id _ => do
      freeTxSkb id
      pure (ForInStep.yield ())) :=
  list_view_spec id (Exact credits) items () _ (fun id _ =>
    preserves_bind (freeTx_preserves id credits) (fun _ => preserves_pure _))

/-- One native TX batch disposal pays one key occurrence, independent of
the number of skbs in the batch. The saved key is tied to the paid loan. -/
theorem tx_dispose_account (pid : PeerId) (items : List SkbId)
    (allocation : Allocation) (remaining : Ledger) :
    Hoare (Queues.TxDisposition.disposeSource pid items allocation.slot)
      (Exact (allocation :: remaining)) (fun _ => Exact remaining) := by
  unfold Queues.TxDisposition.disposeSource
  apply hoare_bind _ _ (freeTxList_preserves items (allocation :: remaining))
  intro _
  apply hoare_bind _ _ (put_account allocation remaining false)
  intro _
  exact preserves_bind (peerPut_preserves (some pid) remaining)
    (fun _ => preserves_pure true)

/-- The literal native poll cleanup pays the saved packet's one key
occurrence. Its subsequent peer payment and packet free leave the remaining
key occurrences exactly funded. -/
theorem rx_cleanup_account (id : SkbId) (pkt : RxPacket) (flag : Bool)
    (allocation : Allocation) (remaining : Ledger) (key : pkt.keypair = allocation.slot) :
    Hoare (Queues.RxCredits.cleanup id pkt flag) (Exact (allocation :: remaining))
      (fun _ => Exact remaining) := by
  unfold Queues.RxCredits.cleanup
  rw [key]
  apply hoare_bind _ _ (put_account allocation remaining false)
  intro _
  apply preserves_bind (peerPut_preserves (some pkt.peer) remaining)
  intro _
  exact preserves_bind (hoare_liftAmbient (AmbientM.branch .rxPollFree flag) (Exact remaining))
    (fun _ => freeRx_preserves id remaining)

end Leanux.Proofs.WG.RetirementSecurity.Credits
