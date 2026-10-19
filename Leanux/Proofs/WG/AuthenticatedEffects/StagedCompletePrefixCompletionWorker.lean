import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixCompletionSelection
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductTx

/-! Every output-history prefix of the actual TX worker is safe. The stronger
result retains the original normal branch or stopped source frontier; logical
prefix safety does not supply an unproved native world for those prefixes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete

theorem worker_body (pid : PeerId) (first : Option (List SkbId))
    (before : CompleteCarrier.Accounted history ledger [] locals w.wg)
    (cached : ∀ p, peerAt w.wg pid = some p → p.txQueue.peeked = first)
    (earlier : All CompleteProduct.Safe history) :
    All CompleteProduct.Safe (runPrefix (TxWorker.body pid first) w history).2 := by
  have paired := Converse.ready_complete first before.complete w
  have allReady := ledger_quiet (TxWorker.ready first)
    (TxWorker.ready_history (fun _ => (none : Option Unit)) (fun _ => rfl) first).1
    (Converse.ready_history first) global_account_safe before earlier
  unfold TxWorker.body
  rw [runPrefix_bind]
  cases readied : runPrefix (TxWorker.ready first) w history with
  | mk outcome middle =>
    rw [readied] at paired allReady
    cases outcome with
    | error stop => exact allReady
    | ok out =>
      obtain ⟨go,u⟩ := out
      obtain ⟨entry,same,shape⟩ := TxWorker.ready_entry first before.entry readied
      have atReady : CompleteCarrier.Accounted middle ledger [] locals u.wg := ⟨entry,paired⟩
      cases go with
      | false => simpa only [Bool.not_false,↓reduceIte,runPrefix_pure] using allReady
      | true =>
        obtain ⟨items,id,packet,chosen,nonempty,_,_⟩ := shape rfl
        have cachedReady : ∀ p, peerAt u.wg pid = some p → p.txQueue.peeked = some items := by
          intro p found
          rw [same] at found
          exact (cached p found).trans chosen
        simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte,chosen,nonempty]
        rw [runPrefix_bind]
        have packetComplete : Complete (runPrefix (CausalJournal.completionOps.packet id) u middle).2 ledger :=
          Converse.focused_access_complete atReady.complete (getTxSkbPrefix id) u
        have allPacket := ledger_quiet (CausalJournal.completionOps.packet id) (Appends.focus _ _ _)
          (Converse.access_history (getTxSkbPrefix id)) global_account_safe atReady allReady
        cases read : runPrefix (CausalJournal.completionOps.packet id) u middle with
        | mk readResult cutHistory =>
          rw [read] at packetComplete allPacket
          cases readResult with
          | error stop => exact allPacket
          | ok out =>
            obtain ⟨head,v⟩ := out
            obtain ⟨atRead,sameRead,_⟩ := TxWorker.packet_entry id entry read
            have cachedRead : ∀ p, peerAt v.wg pid = some p → p.txQueue.peeked = some items := by
              simpa only [sameRead] using cachedReady
            exact after_read pid items head ⟨atRead,packetComplete⟩ cachedRead allPacket

theorem worker_prefix (pid : PeerId)
    (before : CompleteCarrier.Accounted history ledger [] locals w.wg)
    (earlier : All CompleteProduct.Safe history) :
    All CompleteProduct.Safe (runPrefix (CausalJournal.transmit pid) w history).2 := by
  have paired := Converse.peek_complete pid before.complete w
  have allPeek := ledger_quiet (TxSelection.peek pid)
    (TxSelection.peek_history (fun _ => (none : Option Unit)) (fun _ => rfl) pid).1
    (Converse.peek_history pid) global_account_safe before earlier
  rw [TxWorker.transmit_factor,runPrefix_bind]
  cases peeked : runPrefix (TxSelection.peek pid) w history with
  | mk outcome middle =>
    rw [peeked] at paired allPeek
    cases outcome with
    | error stop => exact allPeek
    | ok out =>
      obtain ⟨first,u⟩ := out
      obtain ⟨entry,cached,_⟩ := TxSelection.peek_entry pid before.entry peeked
      exact worker_body pid first ⟨entry,paired⟩ cached allPeek

theorem worker (pid : PeerId)
    (before : CompleteCarrier.Accounted history ledger [] locals w.wg)
    (earlier : All CompleteProduct.Safe history) :
    All CompleteProduct.Safe (runPrefix (CausalJournal.transmit pid) w history).2 ∧
      match (runPrefix (CausalJournal.transmit pid) w history).1 with
      | .error stop => Converse.Worker.TransmitStop ledger locals pid w history stop
          (runPrefix (CausalJournal.transmit pid) w history).2
      | .ok (_,v) => Converse.Worker.Returned ledger locals
          (runPrefix (CausalJournal.transmit pid) w history).2 v :=
  ⟨worker_prefix pid before earlier,Converse.Worker.transmit_cases pid before⟩

/-- Concrete scheduler callback: native allocation and the paired ledger
endpoint stay on the same observed run, with all logical prefixes added. -/
theorem tx_worker (pid : PeerId) :
    Ensures CompleteProduct.Carrier CompleteProduct.Safe (CausalJournal.hooks.transmit pid)
      (fun _ => CompleteProduct.Carrier) := by
  intro w h before
  obtain ⟨suffix,grown,safe,kept⟩ := CompleteProduct.tx_worker pid w h before.1
  obtain ⟨ledger,accounted⟩ := before.1.1
  have allOutput := worker_prefix pid accounted before.2
  refine ⟨suffix,grown,allOutput,?_⟩
  cases result : (runPrefix (CausalJournal.hooks.transmit pid) w h).1 with
  | error stop => trivial
  | ok out => exact ⟨by simpa only [result] using kept,allOutput⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
