import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationTxSelectedDispatch

/-! Readiness and the original selected-head read precede removal. The
normal no-work case retains the same ledger; every Stop names the actual
failed prefix or the reached selected-disposal cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxWorker
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CreateDisposal
set_option pp.structureInstances false

inductive BodyStop (failed : CryptFailure) (ledger : Ledger) (locals : List TxLocalBatch)
    (pid : PeerId) (first : Option (List SkbId)) (w : World)
    (history : List CausalJournal.Event) (stop : Stop) (last : List CausalJournal.Event) : Prop where
  | ready
      (entry : StagedEntry.Inv history ledger [] locals w.wg)
      (performed : runPrefix (TxWorker.ready first) w history = (.error stop,last))
  | packet (u : World) (middle : List CausalJournal.Event) (items : List SkbId) (id : SkbId)
      (readied : runPrefix (TxWorker.ready first) w history = (.ok (true,u),middle))
      (selected : first = some items) (head : items.head? = some id)
      (entry : StagedEntry.Inv middle ledger [] locals u.wg)
      (performed : runPrefix (CausalJournal.completionOps.packet id) u middle = (.error stop,last))
  | afterRead (u v : World) (middle cutHistory : List CausalJournal.Event)
      (items : List SkbId) (id : SkbId) (head : DataPacket)
      (readied : runPrefix (TxWorker.ready first) w history = (.ok (true,u),middle))
      (selected : first = some items) (nonempty : items.head? = some id)
      (read : runPrefix (CausalJournal.completionOps.packet id) u middle = (.ok (head,v),cutHistory))
      (entry : StagedEntry.Inv cutHistory ledger [] locals v.wg)
      (frontier : AfterReadStop failed ledger locals pid items head v cutHistory stop last)

theorem body_cases (failed : CryptFailure) (completed : CryptContract failed)
    (pid : PeerId) (first : Option (List SkbId))
    (before : StagedEntry.Inv history ledger [] locals w.wg)
    (cached : ∀ p, peerAt w.wg pid = some p → p.txQueue.peeked = first) :
    match (runPrefix (body pid first) w history).1 with
    | .error stop => BodyStop failed ledger locals pid first w history stop
        (runPrefix (body pid first) w history).2
    | .ok (_,v) => Returned ledger locals (runPrefix (body pid first) w history).2 v := by
  unfold body
  rw [runPrefix_bind]
  cases readied : runPrefix (ready first) w history with
  | mk outcome middle =>
    cases outcome with
    | error stop => exact .ready before readied
    | ok out =>
      obtain ⟨go,u⟩ := out
      obtain ⟨entry,same,shape⟩ := ready_entry first before readied
      cases go with
      | false =>
        simp only [Bool.not_false,↓reduceIte,runPrefix_pure]
        exact ⟨ledger,.refl _,entry⟩
      | true =>
        obtain ⟨items,id,packet,chosen,nonempty,_,_⟩ := shape rfl
        have atReady : ∀ p, peerAt u.wg pid = some p → p.txQueue.peeked = some items := by
          intro p found
          rw [same] at found
          exact (cached p found).trans chosen
        simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte,chosen,nonempty]
        rw [runPrefix_bind]
        cases read : runPrefix (CausalJournal.completionOps.packet id) u middle with
        | mk readResult cutHistory =>
          cases readResult with
          | error stop => exact .packet u middle items id (by simpa only [chosen] using readied) rfl nonempty entry read
          | ok out =>
            obtain ⟨head,v⟩ := out
            simp only []
            obtain ⟨atRead,sameRead,_⟩ := packet_entry id entry read
            have cachedRead : ∀ p, peerAt v.wg pid = some p → p.txQueue.peeked = some items := by
              simpa only [sameRead] using atReady
            have result := afterRead_cases failed completed pid items head atRead cachedRead
            cases performed : runPrefix (afterRead pid items head) v cutHistory with
            | mk final last =>
              rw [performed] at result
              cases final with
              | error stop => exact .afterRead u v middle cutHistory items id head (by simpa only [chosen] using readied) rfl nonempty read atRead result
              | ok out => exact result

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.TxWorker
