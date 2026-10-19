import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationTxWorkerSource

/-! Actual worker guards and packet reads retain the full fixed entry and
cached queue. Their histories contain only pre-existing completion events. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxWorker
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations
set_option pp.structureInstances false

theorem focused_quiet (action : PrefixM Completion.Event α) (w : World) (history : List CausalJournal.Event) :
    ∃ suffix, (runPrefix (focusPrefix (CausalJournal.Event.old ∘ Journal.completionEvent)
      CausalJournal.completion? action) w history).2 = history ++ suffix ∧
      ∀ event ∈ suffix, birthPackets event = [] := by
  refine ⟨_,rfl,?_⟩
  intro event member
  obtain ⟨localEvent,_,rfl⟩ := List.mem_map.mp member
  cases localEvent <;> rfl

theorem guard (decision : Decision) (flag : Bool) (w : World) (history : List CausalJournal.Event) :
    ∃ v, runPrefix (CausalJournal.completionOps.step (branch decision flag)) w history = (.ok (flag,v),history) ∧
      v.wg = w.wg := by
  let v := {w with ambient := {w.ambient with steps := w.ambient.steps.push {decision := decision, outcome := flag, netRx := w.ambient.netRxSection}}}
  refine ⟨v,?_,rfl⟩
  simpa only [CausalJournal.completionOps,HandshakeSecurity.StagedConservation.SendResult.decorate,
    CompletionEffects.observed,CompletionEffects.focused,CompletionEffects.native,List.map_nil,List.append_nil] using
    focusPrefix_suffix (CausalJournal.Event.old ∘ Journal.completionEvent) CausalJournal.completion?
      (liftPrefix (liftWG (branch decision flag))) w history (.ok (flag,v)) [] (by simp only [List.append_nil]; rfl)

theorem invariant_run (message : String) (w : World) (history : List CausalJournal.Event) :
    runPrefix (CausalJournal.completionOps.step (invariant message) : PrefixM CausalJournal.Event α) w history =
      (.error (.invariant message),history) := by
  simpa only [CausalJournal.completionOps,HandshakeSecurity.StagedConservation.SendResult.decorate,
    CompletionEffects.observed,CompletionEffects.focused,CompletionEffects.native,List.map_nil,List.append_nil] using
    focusPrefix_suffix (CausalJournal.Event.old ∘ Journal.completionEvent) CausalJournal.completion?
      (liftPrefix (liftWG (invariant message : WG.M α))) w history (.error (.invariant message)) []
      (by simp only [List.append_nil]; rfl)

theorem packet_entry (id : SkbId) (before : StagedEntry.Inv history ledger debts locals w.wg)
    (performed : runPrefix (CausalJournal.completionOps.packet id) w history = (.ok (packet,v),last)) :
    StagedEntry.Inv last ledger debts locals v.wg ∧ v.wg = w.wg ∧
      TxDisposition.txPackets w.wg id = some packet := by
  have erases : ErasesPrefix (CausalJournal.completionOps.packet id) (liftWG (getTxSkb id)) :=
    focusPrefix_erases _ _ (Completion.access_erases (getTxSkbPrefix_erases id))
  have full := (erases w history).symm.trans (congrArg Prod.fst performed)
  obtain ⟨suffix,extended,quiet⟩ := focused_quiet (Completion.access (getTxSkbPrefix id)) w history
  change (runPrefix (CausalJournal.completionOps.packet id) w history).2 = _ at extended
  rw [performed] at extended
  change last = history ++ suffix at extended
  rw [liftWG_run] at full
  cases native : ((getTxSkb id).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at full
  | ok out =>
    obtain ⟨⟨result,g⟩,ambient⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨rfl,rfl⟩ := full
    obtain ⟨same,_,d,device,stored⟩ := Packets.getTxSkb_current id w.wg g result w.ambient ambient native
    refine ⟨?_,same,by simp [TxDisposition.txPackets,device,stored]⟩
    rw [extended,same]
    exact before.views suffix quiet rfl rfl rfl rfl rfl rfl

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxWorker
