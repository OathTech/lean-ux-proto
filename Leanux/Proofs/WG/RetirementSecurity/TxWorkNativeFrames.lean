import Leanux.Proofs.WG.RetirementSecurity.TxWorkFrames
import Leanux.Proofs.WG.RetirementSecurity.TxCryptWireFrames

/-! Native TX work-queue frames. These retain pending actor obligations while
packet, peer, key and routing bookkeeping changes other fields. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

private theorem work_modify (initial : List PeerId) (f : Device→Device)
    (same : ∀d,(f d).txWorkQueue=d.txWorkQueue) :
    Preserves (fun w=>queued w=initial) (modifyDev f) :=
  (Leanux.Proofs.WG.RetirementSecurity.TxWork.modify f same).wp (·=initial)

macro "tx_work_step " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getDev; exact (store getDev_sameWGStore).wp (fun s => s = $initial))
  | (rx_retention_head getKeypair
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a k v b before run
     exact (KeyTimes.getKeypair_return _ w v k a b run).1 ▸ before)
  | (rx_retention_head getTxSkb
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a k v b before run
     exact (Packets.getTxSkb_current _ w v k a b run).1 ▸ before)
  | (rx_retention_head setPeer; unfold setPeer)
  | (rx_retention_head setKeypair; unfold setKeypair)
  | (rx_retention_head modifyDev; apply work_modify $initial; intro d; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from Net.M; exact hoare_liftRouting _ _ (fun _ _ h => h))
  | (rx_retention_head liftRouting; exact hoare_liftRouting _ _ (fun _ _ h => h))
  | (rx_retention_head getRouting
     exact hoare_liftRouting ((fun (s : Net.State) => s.toRouting) <$> (get : Net.M Net.State))
       _ (fun _ _ h => h))
  | (rx_retention_head get
     exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head MonadStateOf.get
     exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b before run
     cases run)
  | (rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b before run
     cases run)
  | (rx_retention_head _root_.modify; apply hoare_modify; intro w before; exact before)
  | rx_retention_step)

theorem key_put (kid : Option KeypairId) (now : Bool) : SameView queued (keypairPut kid now) := by
  intro initial
  let P := fun w : WGWorld=>queued w=initial
  have index {α : Type} (action : IndexM α) : Preserves P (monadLift action : WG.M α) := by
    apply hoare_liftIndex action
    intro w d table before device
    simpa [P,queued,device] using before
  change Preserves P _
  unfold keypairPut
  simp only [branch,invariant,refcountDecAndTest,branchCmp,unsupported]
  repeat' first
    | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ P)
    | (allocation_release_lift_from IndexM; exact index _)
    | tx_work_step initial

theorem peer_get (pid : PeerId) : SameView queued (peerGet pid) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold peerGet refcountInc
  simp only [requireNotPending,branch,branchCmp,unsupported]
  repeat' tx_work_step initial

end Leanux.Proofs.WG.RetirementSecurity.TxWork
