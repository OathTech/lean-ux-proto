import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionInteriorPublicationFrames

/-! Source-local coverage interfaces. Packet points are embedded only after
the literal ordered Walk; publication points are fixed withRelease prefixes.
Neither construction infers a current world from a logical safe history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open CompleteCarrier EncryptionPacket
variable {read : RunWitness DataPacket}

theorem ReadPoint.primitive_callback (point : ReadPoint skb ledger debts locals w history read v after)
    (headId : SkbId) (head : RunWitness DataPacket) :
    (runPrefix (encryptionTrace head.value.keypair read.value) v []).1 =
      (runPrefix (crypt headId head skb read) v after).1 ∧
    PrimitiveSafe w.wg (runPrefix (encryptionTrace head.value.keypair read.value) v []).2 := by
  obtain ⟨native,safe⟩ := point.primitive_entries head.value.keypair
  refine ⟨native.trans ?_,safe⟩
  exact (focusPrefix_erases _ _ (WorkerEncryption.crypt_erases headId head skb read) v after).symm

theorem read_failed {skb : SkbId}
    (performed : runPrefix (readPrefix skb) w history = (.error reason,last))
    (headId : SkbId) (head : RunWitness DataPacket) (state : PacketState) :
    runPrefix (iteration headId head skb state) w history = (.error reason,last) := by
  rw [iteration_factor,runPrefix_bind,performed]

theorem ReadPoint.crypt_failed (point : ReadPoint skb ledger debts locals w history read v after)
    (performed : runPrefix (crypt headId head skb read) v after = (.error reason,last)) (state : PacketState) :
    runPrefix (iteration headId head skb state) w history = (.error reason,last) := by
  rw [point.continuation,runPrefix_bind,performed]

def loopReadPrefix (headId : SkbId) (head : RunWitness DataPacket) (done : List SkbId)
    (state : PacketState) (skb : SkbId) : PrefixM CausalJournal.Event (RunWitness DataPacket) := do
  _ ← loop headId head done state
  readPrefix skb

def loopWritePrefix (headId : SkbId) (head : RunWitness DataPacket) (done : List SkbId)
    (state : PacketState) (skb : SkbId) : PrefixM CausalJournal.Event (RunWitness DataPacket × Option (List UInt8)) := do
  _ ← loop headId head done state
  writePrefix headId head skb

theorem walk_read_point (path : Walk headId head done state w history next u middle)
    (point : ReadPoint skb ledger debts locals u middle read v after) :
    runPrefix (loopReadPrefix headId head done state skb) w history = (.ok (read,v),after) := by
  rw [loopReadPrefix,runPrefix_bind,path.run]
  exact point.performed

theorem walk_write_point (path : Walk headId head done state w history next u middle)
    (point : WritePoint headId head skb ledger debts locals u middle read encrypted v after) :
    runPrefix (loopWritePrefix headId head done state skb) w history = (.ok ((read,encrypted),v),after) := by
  rw [loopWritePrefix,runPrefix_bind,path.run]
  exact point.performed

/-- The original loop continuation retains the remaining packets and stops
them on DEAD. A byte-write point cannot be detached from its selected batch. -/
theorem walk_write_continuation (path : Walk headId head done state w history next u middle)
    (point : WritePoint headId head skb ledger debts locals u middle read encrypted v after)
    (rest : List SkbId) :
    runPrefix (loop headId head (done ++ skb :: rest) state) w history =
      runPrefix (writeTail skb next encrypted >>= fun choice =>
        match choice with | .done final => pure final | .yield final => loop headId head rest final) v after := by
  rw [path.continuation,loop_cons,runPrefix_bind,point.continuation]
  rw [runPrefix_bind]
  cases runPrefix (writeTail skb next encrypted) v after with
  | mk result journal =>
    cases result with
    | error stop => rfl
    | ok out => obtain ⟨choice,g⟩ := out; cases choice <;> rfl

structure PublicationPoint (site : PublicationSite) (items : List SkbId) (state : PacketState)
    (ledger : Staged.Obligations.Ledger) (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (w : World) (history : List CausalJournal.Event) (first : SkbId) (pid : PeerId)
    (v : World) (after : List CausalJournal.Event) : Prop where
  performed : runPrefix (publicationPrefixAt site items state) w history = (.ok ((first,pid),v),after)
  accounted : Accounted after ledger debts locals v.wg
  history_eq : after = history

theorem PublicationPoint.continuation
    (point : PublicationPoint site items state ledger debts locals w history first pid v after) :
    runPrefix (ops.publish items state) w history = runPrefix (publicationTailAt site first pid state) v after :=
  publication_continuation point.performed

/-- The marked point contains the actual native setter run, after the same
borrow and queue check. The next source action is scheduling, with no invented
published event between the write and this world. -/
theorem PublicationPoint.marked_native
    (point : PublicationPoint .marked items state ledger debts locals w history first pid v after) :
    ∃ u g,
      (liftWG (AllocatedObligation.Publication.borrowNative items)).run w = (.ok ((first,pid),u)) ∧
      (liftWG (queueCheck pid first)).run u = (.ok ((),g)) ∧
      (liftWG (setTxSkb first fun p => {p with state})).run g = (.ok ((),v)) := by
  have performed := point.performed
  rw [publicationPrefixAt,runPrefix_bind] at performed
  simp only [borrow,runPrefix_lift] at performed
  cases acquired : (liftWG (AllocatedObligation.Publication.borrowNative items)).run w with
  | error reason => simp only [acquired] at performed; cases performed
  | ok out =>
    obtain ⟨⟨head,owner⟩,u⟩ := out
    simp only [acquired,runPrefix_bind,check,mark,runPrefix_lift] at performed
    cases checked : (liftWG (queueCheck owner head)).run u with
    | error reason => simp only [checked] at performed; cases performed
    | ok out =>
      obtain ⟨ignored,g⟩ := out
      cases ignored
      simp only [checked] at performed
      cases written : (liftWG (setTxSkb head fun p => {p with state})).run g with
      | error reason => simp only [written] at performed; cases performed
      | ok out =>
        obtain ⟨ignored,z⟩ := out
        cases ignored
        simp only [written,runPrefix_pure] at performed
        cases performed
        exact ⟨u,g,rfl,checked,written⟩

/-- For every fixed publication site, the actual prefix either fails (and
therefore the original callback fails there) or reaches its real accounted
world with the exact original continuation. This covers normal calls too. -/
theorem publication_points (site : PublicationSite) (items : List SkbId) (state : PacketState)
    (before : Accounted history ledger debts locals w.wg) :
    (∃ reason last, runPrefix (publicationPrefixAt site items state) w history = (.error reason,last) ∧
      runPrefix (ops.publish items state) w history = (.error reason,last)) ∨
    ∃ first pid v after, PublicationPoint site items state ledger debts locals w history first pid v after := by
  cases performed : runPrefix (publicationPrefixAt site items state) w history with
  | mk result after =>
    cases result with
    | error reason =>
      refine Or.inl ⟨reason,after,rfl,?_⟩
      rw [publication_point_factor site,runPrefix_bind,performed]
    | ok out =>
      obtain ⟨⟨first,pid⟩,v⟩ := out
      refine Or.inr ⟨first,pid,v,after,performed,publication_prefix_accounted site before performed,?_⟩
      have quiet := publication_prefix_history site items state w history
      simpa only [performed,List.filterMap_some] using quiet

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionInterior
