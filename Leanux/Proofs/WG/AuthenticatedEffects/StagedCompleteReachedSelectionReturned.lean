import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSelectionPath

/-! Every actual successful nonempty worker selection supplies its original
peek/read/dequeue path. This needs no later callback failure, so it also
anchors interior points of successful crypted and DEAD worker executions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation CompletionBatch Converse TxWorker

theorem selection_returned
    (before : Accounted history ledger [] locals w.wg)
    (performed : runPrefix (workerSelection pid) w history=(.ok (some picked,v),last)) :
    SelectionPath ledger locals pid w history picked v last := by
  rw [workerSelection,runPrefix_bind] at performed
  cases peeked : runPrefix (TxSelection.peek pid) w history with
  | mk result ph =>
      rw [peeked] at performed
      cases result with
      | error reason => cases performed
      | ok pair =>
          obtain ⟨first,pw⟩ := pair
          have paired := peek_complete pid before.complete w
          rw [peeked] at paired
          obtain ⟨atPeek,cached,_⟩ := TxSelection.peek_entry pid before.entry peeked
          have atPeek : Accounted ph ledger [] locals pw.wg := ⟨atPeek,paired⟩
          change runPrefix (bodySelection pid first) pw ph=_ at performed
          unfold bodySelection at performed
          rw [runPrefix_bind] at performed
          cases readied : runPrefix (TxWorker.ready first) pw ph with
          | mk result rh =>
              rw [readied] at performed
              cases result with
              | error reason => cases performed
              | ok pair =>
                  obtain ⟨go,rw⟩ := pair
                  have paired := ready_complete first atPeek.complete pw
                  rw [readied] at paired
                  obtain ⟨atReady,same,shape⟩ := ready_entry first atPeek.entry readied
                  have atReady : Accounted rh ledger [] locals rw.wg := ⟨atReady,paired⟩
                  cases go with
                  | false => simp only [Bool.not_false,↓reduceIte,runPrefix_pure] at performed; cases performed
                  | true =>
                      obtain ⟨items,id,_,chosen,nonempty,_,_⟩ := shape rfl
                      have cachedReady : ∀ p, peerAt rw.wg pid=some p → p.txQueue.peeked=some items := by
                        intro p found
                        rw [same] at found
                        exact (cached p found).trans chosen
                      simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte,chosen,nonempty] at performed
                      rw [runPrefix_bind] at performed
                      cases read : runPrefix (CausalJournal.completionOps.packet id) rw rh with
                      | mk result sh =>
                          rw [read] at performed
                          cases result with
                          | error reason => cases performed
                          | ok pair =>
                              obtain ⟨head,sw⟩ := pair
                              have paired := focused_access_complete atReady.complete (getTxSkbPrefix id) rw
                              change Complete (runPrefix (CausalJournal.completionOps.packet id) rw rh).2 ledger at paired
                              rw [read] at paired
                              obtain ⟨atRead,sameRead,_⟩ := packet_entry id atReady.entry read
                              have atRead : Accounted sh ledger [] locals sw.wg := ⟨atRead,paired⟩
                              have cachedRead : ∀ p, peerAt sw.wg pid=some p → p.txQueue.peeked=some items := by
                                simpa only [sameRead] using cachedReady
                              change runPrefix (afterReadSelection pid items head >>= fun selected=>pure (some selected)) sw sh=_ at performed
                              rw [afterReadSelection,bind_assoc,runPrefix_bind] at performed
                              cases removed : runPrefix (CausalJournal.completionOps.drop pid items) sw sh with
                              | mk result dh =>
                                  rw [removed] at performed
                                  cases result with
                                  | error reason => cases performed
                                  | ok pair =>
                                      obtain ⟨ignored,dw⟩ := pair
                                      cases ignored
                                      have paired := drop_complete pid items atRead.complete sw
                                      rw [removed] at paired
                                      obtain ⟨atDrop,pending⟩ := TxSelection.drop_entry pid items atRead.entry cachedRead removed
                                      have atDrop : Accounted dh ledger [] (⟨.selected,pid,items⟩::locals) dw.wg := ⟨atDrop,paired⟩
                                      obtain ⟨gw,guarded,sameGuard⟩ := guard .txCrypted (head.state==.crypted) dw dh
                                      dsimp only at performed
                                      simp only [runPrefix_bind,guarded,runPrefix_pure,
                                        Prod.mk.injEq,Except.ok.injEq,Option.some.injEq] at performed
                                      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := performed
                                      refine .intro pw rw sw dw ph rh sh id before ?_ ?_ nonempty read atRead
                                        removed atDrop guarded ?_ pending
                                      · simpa only [chosen] using peeked
                                      · simpa only [chosen] using readied
                                      · simpa only [sameGuard] using atDrop

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
