import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionPacketFrames

/-! Ordered original loop prefixes retain the same ledger and actual state.
The failed iteration is reached only after the preceding yielded iterations;
a DEAD result does not execute the remaining packet callbacks. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionPacket
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations CompleteCarrier

theorem iteration_accounted {id : SkbId} (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix (iteration headId head id state) w history = (.ok (next,v),after)) :
    Accounted after ledger debts locals v.wg := by
  unfold iteration at performed
  rw [runPrefix_bind,branch_run] at performed
  dsimp only at performed
  cases packetRun : runPrefix (ops.packet headId head id)
    {w with ambient := CounterWindow.record w.ambient .encWorkerSkbIterate true} history with
  | mk result middle =>
    rw [runPrefix_bind,packetRun] at performed
    cases result with
    | error reason => cases performed
    | ok out =>
      obtain ⟨encrypted,u⟩ := out
      have account : Accounted middle ledger debts locals u.wg :=
        packet_accounted (headId := headId) (head := head) (id := id)
          (w := {w with ambient := CounterWindow.record w.ambient .encWorkerSkbIterate true})
          before packetRun
      dsimp only at performed
      rw [runPrefix_bind,branch_run] at performed
      by_cases success : encrypted.isSome = true
      · simp only [success,↓reduceIte] at performed
        cases written : runPrefix (ops.step (liftWG (setTxSkb id fun p => {p with bytes := encrypted.getD []})))
          {u with ambient := CounterWindow.record u.ambient .encWorkerEncrypted true} middle with
        | mk result last =>
          rw [runPrefix_bind,written] at performed
          cases result with
          | error reason => cases performed
          | ok out =>
            obtain ⟨ignored,g⟩ := out
            cases ignored
            cases performed
            exact bytes_accounted (id := id) (bytes := encrypted.getD [])
              (w := {u with ambient := CounterWindow.record u.ambient .encWorkerEncrypted true})
              account written
      · simp only [success] at performed
        cases performed
        exact account

theorem loop_accounted (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix (loop headId head items state) w history = (.ok (next,v),after)) :
    Accounted after ledger debts locals v.wg := by
  induction items generalizing state w history with
  | nil => cases performed; exact before
  | cons id rest ih =>
    rw [loop_cons,runPrefix_bind] at performed
    cases current : runPrefix (iteration headId head id state) w history with
    | mk result middle =>
      rw [current] at performed
      cases result with
      | error reason => cases performed
      | ok out =>
        obtain ⟨choice,u⟩ := out
        have account := iteration_accounted before current
        cases choice with
        | done next => cases performed; exact account
        | yield next => exact ih account performed

inductive Walk (headId : SkbId) (head : RunWitness DataPacket) :
    List SkbId → PacketState → World → List CausalJournal.Event →
      PacketState → World → List CausalJournal.Event → Prop where
  | nil : Walk headId head [] state w history state w history
  | cons {id : SkbId} (performed : runPrefix (iteration headId head id state) w history = (.ok (.yield next,u),middle))
      (tail : Walk headId head rest next u middle last v after) :
      Walk headId head (id :: rest) state w history last v after

theorem Walk.run (path : Walk headId head done state w history next v after) :
    runPrefix (loop headId head done state) w history = (.ok (next,v),after) := by
  induction path with
  | nil => rfl
  | cons performed tail ih => rw [loop_cons,runPrefix_bind,performed]; exact ih

theorem Walk.continuation (path : Walk headId head done state w history next v after)
    (remaining : List SkbId) :
    runPrefix (loop headId head (done ++ remaining) state) w history =
      runPrefix (loop headId head remaining next) v after := by
  induction path with
  | nil => rfl
  | cons performed tail ih => rw [List.cons_append,loop_cons,runPrefix_bind,performed]; exact ih

theorem Walk.accounted (path : Walk headId head done state w history next v after)
    (before : Accounted history ledger debts locals w.wg) : Accounted after ledger debts locals v.wg :=
  loop_accounted before path.run

/-- Every actual loop failure occurs at an iteration after a literal list
prefix of successful yielded iterations. The saved world is that prefix's
actual output, not a witness obtained from history safety. -/
theorem loop_failed (before : Accounted history ledger debts locals w.wg)
    (failed : runPrefix (loop headId head items state) w history = (.error reason,last)) :
    ∃ done id rest next u middle,
      items = done ++ (id :: rest) ∧ Walk headId head done state w history next u middle ∧
      Accounted middle ledger debts locals u.wg ∧
      runPrefix (iteration headId head id next) u middle = (.error reason,last) := by
  induction items generalizing state w history with
  | nil => cases failed
  | cons id rest ih =>
    rw [loop_cons,runPrefix_bind] at failed
    cases current : runPrefix (iteration headId head id state) w history with
    | mk result middle =>
      rw [current] at failed
      cases result with
      | error stop => cases failed; exact ⟨[],id,rest,state,w,history,rfl,.nil,before,current⟩
      | ok out =>
        obtain ⟨choice,u⟩ := out
        have account := iteration_accounted before current
        cases choice with
        | done next => cases failed
        | yield next =>
          obtain ⟨done,skb,remaining,flag,g,journal,shape,path,atCut,cut⟩ := ih account failed
          exact ⟨id :: done,skb,remaining,flag,g,journal,by simp only [List.cons_append,shape],
            .cons current path,atCut,cut⟩

theorem publication_entry (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix (loop headId head items .crypted) w history = (.ok (state,u),middle)) :
    ∃ v, runPrefix (publicationPrefix headId head items) w history = (.ok (state,v),middle) ∧
      Accounted middle ledger debts locals v.wg ∧
      runPrefix (HandshakeSecurity.StagedDisposal.EncryptionSource.afterHead ops items headId head) w history =
        runPrefix (publish items state) v middle := by
  have account := loop_accounted before performed
  obtain ⟨v,guarded,same⟩ := guard_total state u middle
  have reached : runPrefix (publicationPrefix headId head items) w history = (.ok (state,v),middle) := by
    rw [publicationPrefix,runPrefix_bind,performed]
    change runPrefix (guard state >>= fun _ => pure state) u middle = _
    rw [runPrefix_bind,guarded]
    rfl
  refine ⟨v,reached,same ▸ account,?_⟩
  rw [publication_factor,runPrefix_bind,reached]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionPacket
