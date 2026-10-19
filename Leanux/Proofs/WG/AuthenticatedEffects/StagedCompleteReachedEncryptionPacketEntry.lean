import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionPacketPaths

/-! The captured head and packet walk belong to the same actual callback
entry. Publication keeps the original selected batch, and the outer return
receipt still uses the original callback's entry world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionPacket
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open HandshakeSecurity.StagedDisposal Staged.Obligations CompleteCarrier

theorem head_prefix_current (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix (headPrefix items) w history = (.ok ((headId,head),u),middle)) :
    items.head? = some headId ∧
      head.before = {w with ambient := CounterWindow.record w.ambient .encWorkerConsumed true} ∧
      head.after = u ∧ head.Valid (liftWG (getTxSkb headId)) ∧
      Accounted middle ledger debts locals u.wg ∧ middle = history := by
  rw [headPrefix,runPrefix_bind,branch_run] at performed
  dsimp only at performed
  cases selected : items.head? with
  | none =>
    simp only [selected,step_eq] at performed
    cases performed
  | some first =>
    simp only [selected] at performed
    cases captured : runPrefix (ops.head first)
      {w with ambient := CounterWindow.record w.ambient .encWorkerConsumed true} history with
    | mk result after =>
      rw [runPrefix_bind,captured] at performed
      cases result with
      | error reason => cases performed
      | ok out =>
        obtain ⟨receipt,v⟩ := out
        cases performed
        obtain ⟨atEntry,atExit,valid,same,rfl⟩ := head_current captured
        exact ⟨rfl,atEntry,atExit,valid,same ▸ before,rfl⟩

def callbackPublicationPrefix (items : List SkbId) :
    PrefixM CausalJournal.Event (SkbId × RunWitness DataPacket × PacketState) := do
  let (headId,head) ← headPrefix items
  let state ← publicationPrefix headId head items
  pure (headId,head,state)

structure PublicationPath (items : List SkbId) (w : World) (history : List CausalJournal.Event)
    (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (headId : SkbId) (head : RunWitness DataPacket) (state : PacketState)
    (v : World) (after : List CausalJournal.Event) : Prop where
  selected : items.head? = some headId
  captured : ∃ u middle, runPrefix (headPrefix items) w history = (.ok ((headId,head),u),middle) ∧
    Accounted middle ledger debts locals u.wg ∧
    runPrefix (publicationPrefix headId head items) u middle = (.ok (state,v),after)
  performed : runPrefix (callbackPublicationPrefix items) w history = (.ok ((headId,head,state),v),after)
  accounted : Accounted after ledger debts locals v.wg

theorem publication_path (before : Accounted history ledger debts locals w.wg)
    (captured : runPrefix (headPrefix items) w history = (.ok ((headId,head),u),middle))
    (walked : runPrefix (loop headId head items .crypted) u middle = (.ok (state,g),after)) :
    ∃ v, PublicationPath items w history ledger debts locals headId head state v after := by
  obtain ⟨selected,_,_,_,account,_⟩ := head_prefix_current before captured
  obtain ⟨v,reached,kept,_⟩ := publication_entry account walked
  refine ⟨v,selected,⟨u,middle,captured,account,reached⟩,?_,kept⟩
  rw [callbackPublicationPrefix,runPrefix_bind,captured]
  change runPrefix (publicationPrefix headId head items >>= fun state => pure (headId,head,state)) u middle = _
  rw [runPrefix_bind,reached]
  rfl

theorem PublicationPath.tail_run
    (path : PublicationPath items w history ledger debts locals headId head state v after) :
    runPrefix (EncryptionSource.tail ops (some items)) w history = runPrefix (publish items state) v after := by
  obtain ⟨u,middle,captured,_,reached⟩ := path.captured
  rw [tail_factor items headId path.selected,runPrefix_bind,captured]
  change runPrefix (EncryptionSource.afterHead ops items headId head) u middle = _
  rw [publication_factor,runPrefix_bind,reached]

/-- The original continuation, including a failed publication, is retained.
Its successful outer receipt names the callback's original entry world. -/
theorem PublicationPath.original
    (path : PublicationPath items w history ledger debts locals headId head state v after) :
    runPrefix (CausalJournal.encrypt (some items)) w history =
      match runPrefix (publish items state) v after with
      | (.error reason,last) => (.error reason,last)
      | (.ok (value,g),last) =>
        (.ok (value,g),last ++ [.old (.encryptionReturn (some items) ⟨value,w,g⟩)]) := by
  rw [encrypt_run,path.tail_run]
  cases runPrefix (publish items state) v after with
  | mk result last => cases result <;> rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionPacket
