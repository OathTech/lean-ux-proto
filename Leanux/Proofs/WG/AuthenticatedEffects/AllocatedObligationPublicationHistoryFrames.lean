import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPublicationFrames
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPublicationSource
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationAdmissionHistoryFrames

/-! History and state are transported independently through actual DEAD
publication. The history proof includes the nested peer-release observer;
native erasure is used only for the completed state relation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Publication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open HandshakeSecurity.StagedDisposal Staged.Obligations QueueHandoff
open CausalJournal.CallbackQuiet
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem history (ρ : CausalJournal.Event → Option F)
    (old : ∀ e, ρ (CausalJournal.txEvent e) = none)
    (disposal : ∀ e, ρ (.stagedDisposal e) = none)
    (items : List SkbId) (state : PacketState) :
    ProductQuiet ρ (TxSource.publish Admission.actualOps items state) := by
  apply product_of_history
  intro before
  unfold TxSource.publish Admission.actualOps
  simp only [TxSource.observed,TxSource.Ops.focus]
  repeat' first
    | (driver_history_head TxSource.releaseObserved; exact product_history (release ρ old disposal _) before)
    | (driver_history_head focusPrefix; exact product_history
        (product_focus ρ CausalJournal.txEvent CausalJournal.txEvent? old _) before)
    | driver_product_history_step

theorem birth_quiet (items : List SkbId) (state : PacketState) (w : World)
    (h : List CausalJournal.Event) :
    ∃ suffix, (runPrefix (TxSource.publish Admission.actualOps items state) w h).2 = h ++ suffix ∧
      ∀ event ∈ suffix, birthPackets event = [] := by
  classical
  let ρ : CausalJournal.Event → Option Unit := fun event => if birthPackets event = [] then none else some ()
  have quiet := history ρ (fun _ => by simp [ρ,birthPackets,CausalJournal.txEvent])
    (fun _ => by simp [ρ,birthPackets]) items state
  obtain ⟨suffix,extended⟩ := quiet.1 w h
  refine ⟨suffix,extended,?_⟩
  have filtered := quiet.2 w h
  rw [extended,List.filterMap_append] at filtered
  have empty : suffix.filterMap ρ = [] := List.append_right_eq_self.mp filtered
  intro event member
  by_cases nonempty : birthPackets event = []
  · exact nonempty
  have bad : () ∈ suffix.filterMap ρ := List.mem_filterMap.mpr ⟨event,member,by simp [ρ,nonempty]⟩
  rw [empty] at bad
  cases bad

/-- A normally returning original publication preserves the same complete
canonical ledger and queue ownership. The paired borrow supplies the
nonfinal-repayment fact used by the native staged-queue frame. -/
theorem returned (items : List SkbId) (state : PacketState)
    (owned : Owned ledger debts locals h w)
    (performed : runPrefix (TxSource.publish Admission.actualOps items state) w h =
      (.ok ((),v),last)) : Owned ledger debts locals last v := by
  have full := (Admission.publication_erases items state w h).symm.trans (congrArg Prod.fst performed)
  obtain ⟨suffix,extended,quiet⟩ := birth_quiet items state w h
  rw [performed] at extended
  change last = h ++ suffix at extended
  rw [liftWG_run] at full
  cases native : ((enqueuePerPeerTx items state).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at full
  | ok out =>
    obtain ⟨⟨result,g⟩,ambient⟩ := out
    cases result
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨_,rfl⟩ := full
    have material := (ProjectedAction.iff_run_ambient _ _ _).mp
      (Admission.publication items state) w.wg w.ambient () g ambient native
    have queues := (ProjectedAction.iff_run_ambient _ _ _).mp
      (staged items state) w.wg w.ambient () g ambient native
    refine ⟨?_,owned.2.1.publish items state _ _ native,owned.2.2.publish items state _ _ native⟩
    rw [extended]
    exact owned.1.quiet_views suffix quiet (congrArg Prod.fst material) queues
      (congrArg Prod.snd material)

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Publication
