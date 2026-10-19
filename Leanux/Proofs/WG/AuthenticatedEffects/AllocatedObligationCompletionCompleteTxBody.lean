import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteTxSelection

/-! Actual TX worker source transport with Entry and terminal completeness
on the same ledger. Normal paths retain their branch witness; stopped paths
retain the reached native cut and source run. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse.Worker
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open StagedEntry.CompleteCarrier StagedTerminalComplete TxWorker
open Staged.Obligations CreateDisposal
set_option pp.structureInstances false

inductive BodyStop (ledger : Ledger) (locals : List TxLocalBatch)
    (pid : PeerId) (first : Option (List SkbId)) (w : World)
    (history : List CausalJournal.Event) (stop : Stop) (last : List CausalJournal.Event) : Prop where
  | ready
      (entry : Accounted history ledger [] locals w.wg)
      (performed : runPrefix (TxWorker.ready first) w history = (.error stop,last))
  | packet (u : World) (middle : List CausalJournal.Event) (items : List SkbId) (id : SkbId)
      (readied : runPrefix (TxWorker.ready first) w history = (.ok (true,u),middle))
      (selected : first = some items) (head : items.head? = some id)
      (entry : Accounted middle ledger [] locals u.wg)
      (performed : runPrefix (CausalJournal.completionOps.packet id) u middle = (.error stop,last))
  | afterRead (u v : World) (middle cutHistory : List CausalJournal.Event)
      (items : List SkbId) (id : SkbId) (head : DataPacket)
      (readied : runPrefix (TxWorker.ready first) w history = (.ok (true,u),middle))
      (selected : first = some items) (nonempty : items.head? = some id)
      (read : runPrefix (CausalJournal.completionOps.packet id) u middle = (.ok (head,v),cutHistory))
      (entry : Accounted cutHistory ledger [] locals v.wg)
      (frontier : AfterReadStop ledger locals pid items head v cutHistory stop last)

theorem body_cases
    (pid : PeerId) (first : Option (List SkbId))
    (before : Accounted history ledger [] locals w.wg)
    (cached : ∀ p, peerAt w.wg pid = some p → p.txQueue.peeked = first) :
    match (runPrefix (TxWorker.body pid first) w history).1 with
    | .error stop => BodyStop ledger locals pid first w history stop
        (runPrefix (TxWorker.body pid first) w history).2
    | .ok (_,v) => Returned ledger locals (runPrefix (TxWorker.body pid first) w history).2 v := by
  have paired := ready_complete first before.complete w
  unfold TxWorker.body
  rw [runPrefix_bind]
  cases readied : runPrefix (TxWorker.ready first) w history with
  | mk outcome middle =>
    rw [readied] at paired
    cases outcome with
    | error stop => exact .ready before readied
    | ok out =>
      obtain ⟨go,u⟩ := out
      obtain ⟨entry,same,shape⟩ := ready_entry first before.entry readied
      have entry : Accounted middle ledger [] locals u.wg := ⟨entry,paired⟩
      cases go with
      | false =>
        simp only [Bool.not_false,↓reduceIte,runPrefix_pure]
        exact .idle entry
      | true =>
        obtain ⟨items,id,packet,chosen,nonempty,_,_⟩ := shape rfl
        have atReady : ∀ p, peerAt u.wg pid = some p → p.txQueue.peeked = some items := by
          intro p found
          rw [same] at found
          exact (cached p found).trans chosen
        simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte,chosen,nonempty]
        rw [runPrefix_bind]
        have packetComplete : Complete (runPrefix (CausalJournal.completionOps.packet id) u middle).2 ledger :=
          focused_access_complete entry.complete (getTxSkbPrefix id) u
        cases read : runPrefix (CausalJournal.completionOps.packet id) u middle with
        | mk readResult cutHistory =>
          rw [read] at packetComplete
          cases readResult with
          | error stop => exact .packet u middle items id (by simpa only [chosen] using readied) rfl nonempty entry read
          | ok out =>
            obtain ⟨head,v⟩ := out
            simp only []
            obtain ⟨atRead,sameRead,_⟩ := packet_entry id entry.entry read
            have atRead : Accounted cutHistory ledger [] locals v.wg := ⟨atRead,packetComplete⟩
            have cachedRead : ∀ p, peerAt v.wg pid = some p → p.txQueue.peeked = some items := by
              simpa only [sameRead] using atReady
            have result := afterRead_cases pid items head atRead cachedRead
            cases performed : runPrefix (TxWorker.afterRead pid items head) v cutHistory with
            | mk final last =>
              rw [performed] at result
              cases final with
              | error stop => exact .afterRead u v middle cutHistory items id head (by simpa only [chosen] using readied) rfl nonempty read atRead result
              | ok out => exact result

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse.Worker
