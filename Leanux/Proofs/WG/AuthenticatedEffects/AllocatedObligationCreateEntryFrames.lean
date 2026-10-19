import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueueSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReleaseSource
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationRefusalFreeLoop
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationAdmissionFrontFrames

/-! Full semantic entry frames at the unchanged-ledger create cuts. Native
bounds and ownership are discharged independently from actual history
extension; final peer settlement has its separate source adapter. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations QueueHandoff HandshakeSecurity.StagedDisposal
set_option pp.structureInstances false
set_option maxHeartbeats 600000

theorem guard_entry (decision : Decision) (flag : Bool)
    (before : StagedEntry.Inv history ledger debts locals w.wg) :
    ∃ v, runPrefix (Admission.actualOps.step (branch decision flag)) w history = (.ok (flag,v),history) ∧
      StagedEntry.Inv history ledger debts locals v.wg := by
  obtain ⟨v,run,owned,bounds⟩ := CreateDisposal.guard_total decision flag
    (StagedEntry.Queue.owned before) before.packets
  exact ⟨v,run,⟨owned.1,before.justified,before.allocationLinks,before.noSelected,bounds,owned.2.1,owned.2.2⟩⟩

theorem read_peer_entry (pid : PeerId) (before : StagedEntry.Inv history ledger debts locals w.wg)
    (performed : runPrefix (Admission.actualOps.access (getPeerMixed pid)) w history = (.ok (p,v),last)) :
    StagedEntry.Inv last ledger debts locals v.wg := by
  have owned := Admission.read_peer_entry pid (StagedEntry.Queue.owned before) performed
  have keeps : Preserves Packets.Inv (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b bounded native
    simpa only [(Peers.getPeer_current pid w v p a b native).1] using bounded
  have bounds := StagedEntry.Queue.focused_bounds
    (TxDisposition.nativeAccess_erases (getPeerMixed_erases pid)) keeps before.packets performed
  obtain ⟨suffix,extended,_⟩ := focused_quiet (TxDisposition.nativeAccess (getPeerMixed pid)) w history
  change (runPrefix (Admission.actualOps.access (getPeerMixed pid)) w history).2 = _ at extended
  rw [performed] at extended
  change last = history ++ suffix at extended
  rw [extended] at owned ⊢
  exact StagedEntry.Queue.semantic before suffix owned bounds

theorem key_repayment_entry (first : SkbId) (before : StagedEntry.Inv history ledger debts locals w.wg)
    (performed : runPrefix (CreateDisposal.keyRepayment first) w history = (.ok ((),v),last)) :
    StagedEntry.Inv last ledger debts locals v.wg := by
  obtain ⟨owned,bounds⟩ := CreateDisposal.key_repayment_returned first
    (StagedEntry.Queue.owned before) before.packets performed
  have appends : Appends (CreateDisposal.keyRepayment first) :=
    Appends.bind (Appends.focus _ _ _) (fun _ => Appends.focus _ _ _)
  obtain ⟨suffix,extended⟩ := appends w history
  rw [performed] at extended
  change last = history ++ suffix at extended
  rw [extended] at owned ⊢
  exact StagedEntry.Queue.semantic before suffix owned bounds

theorem publication_bounds (items : List SkbId) (state : PacketState) :
    Preserves Packets.Inv (enqueuePerPeerTx items state) := by
  have readTx (skb : SkbId) : Preserves Packets.Inv (getTxSkb skb) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a packet v b bounded native
    simpa only [(Packets.getTxSkb_current skb w v packet a b native).1] using bounded
  have readPeer (pid : PeerId) : Preserves Packets.Inv (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a packet v b bounded native
    simpa only [(Peers.getPeer_current pid w v packet a b native).1] using bounded
  have getPeerRef (pid : PeerId) : Preserves Packets.Inv (peerGet pid) :=
    ((StagingOccurrences.peer_get_geometry pid).of_factor Prod.fst Packets.snapshot (fun _ => rfl)).wp Bounded
  have putPeerRef (pid : Option PeerId) : Preserves Packets.Inv (peerPut pid) :=
    ((StagingOccurrences.peer_put_geometry pid).of_factor Prod.fst Packets.snapshot (fun _ => rfl)).wp Bounded
  unfold enqueuePerPeerTx cpumaskChooseOnline
  simp only [Nat.mod_one,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (allocation_release_head getTxSkb; exact readTx _)
    | (allocation_release_head getPeer; exact readPeer _)
    | (allocation_release_head peerGet; exact getPeerRef _)
    | (allocation_release_head peerPut; exact putPeerRef _)
    | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
    | (allocation_release_head setTxSkb; exact StagedEntry.Queue.mark_bounds _ _)
    | (allocation_release_head getDev; exact StagedEntry.Queue.store_bounds getDev_sameWGStore)
    | (allocation_release_head setPeer; exact StagedEntry.Queue.modify_bounds _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
    | (allocation_release_head modifyDev; exact StagedEntry.Queue.modify_bounds _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
    | (allocation_release_head cpumaskNextOnlineFrom; exact StagedEntry.Queue.store_bounds (cpumaskNextOnlineFrom_sameStore _))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (allocation_release_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | (allocation_release_head ForIn.forIn
       apply list_view_spec id Packets.Inv
       intro x b
       change Preserves Packets.Inv _)
    | (allocation_release_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
    | (allocation_release_head peekQueuedUnit; exact hoare_liftAmbient (AmbientM.peekQueuedUnit _ _) _)
    | (allocation_release_head recordQueued; exact hoare_liftAmbient (AmbientM.recordQueued _ _) _)
    | allocation_release_step

theorem publication_entry (items : List SkbId) (state : PacketState)
    (before : StagedEntry.Inv history ledger debts locals w.wg)
    (performed : runPrefix (TxSource.publish Admission.actualOps items state) w history = (.ok ((),v),last)) :
    StagedEntry.Inv last ledger debts locals v.wg := by
  have owned := Publication.returned items state (StagedEntry.Queue.owned before) performed
  obtain ⟨suffix,extended,_⟩ := Publication.birth_quiet items state w history
  rw [performed] at extended
  change last = history ++ suffix at extended
  have full := (Admission.publication_erases items state w history).symm.trans (congrArg Prod.fst performed)
  rw [liftWG_run] at full
  cases native : ((enqueuePerPeerTx items state).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at full
  | ok out =>
    obtain ⟨⟨ignored,g⟩,ambient⟩ := out
    cases ignored
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨_,rfl⟩ := full
    have bounds := (hoare_iff_run_ambient _ _ _).mp (publication_bounds items state)
      w.wg w.ambient () g ambient before.packets native
    rw [extended] at owned ⊢
    exact StagedEntry.Queue.semantic before suffix owned bounds

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateEntry
