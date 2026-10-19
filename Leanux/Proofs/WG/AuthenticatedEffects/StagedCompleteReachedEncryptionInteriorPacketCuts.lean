import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionInteriorPacketSource

/-! Fixed read and write points of one original packet iteration. Each point
retains its actual native prefix, the same ledger, and the original suffix.
The cases cover successful iterations as well as failed child calls. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CompleteCarrier EncryptionPacket
variable {read : RunWitness DataPacket}

theorem read_current {skb : SkbId} (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix (readPrefix skb) w history = (.ok (read,v),after)) :
    read.before = {w with ambient := CounterWindow.record w.ambient .encWorkerSkbIterate true} ∧
      read.after = v ∧ read.Valid (liftWG (getTxSkb skb)) ∧
      v.wg = w.wg ∧ after = history ∧ Accounted after ledger debts locals v.wg := by
  rw [readPrefix,runPrefix_bind,branch_run] at performed
  have current := head_current (id := skb) (by simpa only [head_eq] using performed)
  exact ⟨current.1,current.2.1,current.2.2.1,current.2.2.2.1,current.2.2.2.2,
    by rw [current.2.2.2.1,current.2.2.2.2]; exact before⟩

theorem crypt_accounted (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix (crypt headId head skb read) w history = (.ok (value,v),after)) :
    Accounted after ledger debts locals v.wg :=
  focused_accounted _ _ (fun _ => rfl) (fun _ _ => rfl) _ _
    (WorkerEncryption.crypt_erases headId head skb read) (Encrypt.packet _ _) before performed

structure ReadPoint (skb : SkbId) (ledger : Staged.Obligations.Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List TxLocalBatch) (w : World) (history : List CausalJournal.Event)
    (read : RunWitness DataPacket) (v : World) (after : List CausalJournal.Event) : Prop where
  performed : runPrefix (readPrefix skb) w history = (.ok (read,v),after)
  current : read.before = {w with ambient := CounterWindow.record w.ambient .encWorkerSkbIterate true}
  returned : read.after = v
  native : read.Valid (liftWG (getTxSkb skb))
  same : v.wg = w.wg
  history_eq : after = history
  accounted : Accounted after ledger debts locals v.wg

theorem read_point {skb : SkbId} (before : Accounted history ledger debts locals w.wg)
    (performed : runPrefix (readPrefix skb) w history = (.ok (read,v),after)) :
    ReadPoint skb ledger debts locals w history read v after := by
  obtain ⟨current,returned,native,same,history_eq,accounted⟩ := read_current before performed
  exact ⟨performed,current,returned,native,same,history_eq,accounted⟩

theorem ReadPoint.continuation (point : ReadPoint skb ledger debts locals w history read v after)
    (headId : SkbId) (head : RunWitness DataPacket) (state : PacketState) :
    runPrefix (iteration headId head skb state) w history =
      runPrefix (crypt headId head skb read >>= afterCrypt skb state) v after := by
  rw [iteration_factor,runPrefix_bind,point.performed]

/-- The read that feeds encryption is the actual current read. Its source-local
primitive entries share this input WG state, even if a later primitive stops. -/
theorem ReadPoint.primitive_entries (point : ReadPoint skb ledger debts locals w history read v after)
    (slot : KeypairId) :
    (runPrefix (encryptionTrace slot read.value) v []).1 = (encryptPacket Env.checksumHelp slot read.value).run v ∧
      PrimitiveSafe w.wg (runPrefix (encryptionTrace slot read.value) v []).2 := by
  obtain ⟨native,safe⟩ := encryption_interiors slot read.value v
  exact ⟨native,by simpa only [point.same] using safe⟩

structure WritePoint (headId : SkbId) (head : RunWitness DataPacket) (skb : SkbId)
    (ledger : Staged.Obligations.Ledger) (debts : List AllocatedObligation.CleanupDebt) (locals : List TxLocalBatch)
    (w : World) (history : List CausalJournal.Event) (read : RunWitness DataPacket)
    (encrypted : Option (List UInt8)) (v : World) (after : List CausalJournal.Event) : Prop where
  performed : runPrefix (writePrefix headId head skb) w history = (.ok ((read,encrypted),v),after)
  read_entry : ∃ u middle, ReadPoint skb ledger debts locals w history read u middle ∧
    ∃ g, runPrefix (crypt headId head skb read) u middle = (.ok (encrypted,g),after) ∧
      v = {g with ambient := CounterWindow.record g.ambient .encWorkerEncrypted encrypted.isSome}
  accounted : Accounted after ledger debts locals v.wg

theorem WritePoint.continuation (point : WritePoint headId head skb ledger debts locals w history read encrypted v after)
    (state : PacketState) :
    runPrefix (iteration headId head skb state) w history = runPrefix (writeTail skb state encrypted) v after := by
  rw [write_factor,runPrefix_bind,point.performed]

/-- Unconditional source coverage through the actual read and encryption
children. A successful crypt call reaches the fixed byte-write guard point;
a failed child keeps its real input and failed outcome. -/
theorem packet_points {skb : SkbId} (headId : SkbId) (head : RunWitness DataPacket)
    (before : Accounted history ledger debts locals w.wg) :
    (∃ stop last, runPrefix (readPrefix skb) w history = (.error stop,last)) ∨
    ∃ read u middle, ReadPoint skb ledger debts locals w history read u middle ∧
      ((∃ stop last, runPrefix (crypt headId head skb read) u middle = (.error stop,last)) ∨
       ∃ encrypted v after, WritePoint headId head skb ledger debts locals w history read encrypted v after) := by
  cases captured : runPrefix (readPrefix skb) w history with
  | mk result middle =>
    cases result with
    | error stop => exact Or.inl ⟨stop,middle,rfl⟩
    | ok out =>
      obtain ⟨read,u⟩ := out
      have point := read_point before captured
      refine Or.inr ⟨read,u,middle,point,?_⟩
      cases encryptedRun : runPrefix (crypt headId head skb read) u middle with
      | mk result after =>
        cases result with
        | error stop => exact Or.inl ⟨stop,after,rfl⟩
        | ok out =>
          obtain ⟨encrypted,g⟩ := out
          have account := crypt_accounted point.accounted encryptedRun
          refine Or.inr ⟨encrypted,{g with ambient := CounterWindow.record g.ambient .encWorkerEncrypted encrypted.isSome},after,?_,
            ⟨u,middle,point,g,encryptedRun,rfl⟩,account⟩
          rw [writePrefix,runPrefix_bind,captured]
          change runPrefix (crypt headId head skb read >>= fun encrypted => do
            _ ← ops.step (branch .encWorkerEncrypted encrypted.isSome)
            pure (read,encrypted)) u middle = _
          rw [runPrefix_bind,encryptedRun]
          simp only [runPrefix_bind,branch_run,runPrefix_pure]

/-- Every byte-setter outcome is the original native call. Successful writes
preserve the same ledger; failures keep the reached pre-write world. -/
theorem WritePoint.write_cases (point : WritePoint headId head skb ledger debts locals w history read encrypted v after)
    (state : PacketState) :
    (encrypted = none ∧ runPrefix (iteration headId head skb state) w history = (.ok (.done .dead,v),after)) ∨
    ∃ bytes, encrypted = some bytes ∧
      ((∃ stop last, runPrefix (ops.step (liftWG (setTxSkb skb fun p => {p with bytes}))) v after = (.error stop,last) ∧
        runPrefix (iteration headId head skb state) w history = (.error stop,last)) ∨
      (∃ g last, runPrefix (ops.step (liftWG (setTxSkb skb fun p => {p with bytes}))) v after = (.ok ((),g),last) ∧
        Accounted last ledger debts locals g.wg ∧
        runPrefix (iteration headId head skb state) w history = (.ok (.yield state,g),last))) := by
  rw [point.continuation]
  cases encrypted with
  | none => exact Or.inl ⟨rfl,rfl⟩
  | some bytes =>
    refine Or.inr ⟨bytes,rfl,?_⟩
    cases written : runPrefix (ops.step (liftWG (setTxSkb skb fun p => {p with bytes}))) v after with
    | mk result last =>
      cases result with
      | error stop =>
        refine Or.inl ⟨stop,last,rfl,?_⟩
        change runPrefix (ops.step (liftWG (setTxSkb skb fun p => {p with bytes})) >>= fun _ => pure (ForInStep.yield state)) v after = _
        rw [runPrefix_bind,written]
      | ok out =>
        obtain ⟨ignored,g⟩ := out
        cases ignored
        refine Or.inr ⟨g,last,rfl,bytes_accounted point.accounted written,?_⟩
        change runPrefix (ops.step (liftWG (setTxSkb skb fun p => {p with bytes})) >>= fun _ => pure (ForInStep.yield state)) v after = _
        rw [runPrefix_bind,written]
        rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionInterior
