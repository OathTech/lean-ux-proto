import Leanux.Proofs.WG.KeyTimes.ReceiveAttempts
import Leanux.Proofs.WG.Lifetimes.TxStaging

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! One original staging call, observed at the completed allocation / submit
boundary. Captured WG and Ambient endpoints are proof-side execution witnesses only. -/
namespace Leanux.Proofs.WG.KeyTimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.CounterWindow

structure TxAdmission where
  peer : PeerId
  slot : KeypairId
  keyRead : WGRunWitness Keypair
  clockRead : WGRunWitness Int64
  packets : List DataPacket
  allocation : WGRunWitness (List SkbId)

def TxAdmission.Valid (a : TxAdmission) : Prop :=
  a.keyRead.Valid (getKeypair a.slot) ∧
  a.keyRead.value.sending.isValid = true ∧
  a.clockRead.Valid (hiddenClock64 .birthdateExpired) ∧
  ¬ deadline a.keyRead.value.sending.birthdate REJECT_AFTER_TIME ≤ a.clockRead.value ∧
  (∀ p ∈ a.packets, p.peer = a.peer ∧ p.keypair = a.slot ∧ p.nonce < REJECT_AFTER_MESSAGES) ∧
  a.allocation.Valid (a.packets.mapM newTxSkb)

def stagingObserved (pid : PeerId) : WGPrefix TxAdmission Unit := do
  let p ← liftWGPrefix (getPeer pid)
  if ← liftWGPrefix (branch .stagedEmpty p.staged.isEmpty) then return
  let packets := p.staged
  liftWGPrefix (setPeer pid {p with staged := []})
  let keypair ← liftWGPrefix (keypairGet p.keypairCurrent)
  let outNokey (invalid : Bool) := liftWGPrefix (Lifetimes.stagedOutNokey pid packets keypair invalid)
  if ← liftWGPrefix (branch .stagedNoKeypair keypair.isNone) then return ← outNokey false
  let some id := keypair | liftWGPrefix (invariant "unreachable")
  let keyRead ← captureWGRun (getKeypair id)
  let k := keyRead.value
  if ← liftWGPrefix (branch .stagedKeyInvalid !k.sending.isValid) then return ← outNokey false
  let clockRead ← captureWGRun (hiddenClock64 .birthdateExpired)
  let lhs := deadline k.sending.birthdate REJECT_AFTER_TIME
  if ← liftWGPrefix (branchCmp .stagedBirthdateExpired (lhs ≤ clockRead.value) lhs.toInt clockRead.value.toInt) then
    return ← outNokey true
  let mut packetsCb : List DataPacket := []
  for pkt in packets do
    _ ← liftWGPrefix (branch .stagedNonceIterate true)
    let ds ← liftWGPrefix (ipTunnelEcnEncap pkt)
    let k ← liftWGPrefix (getKeypair id)
    let nonce := k.sendingCounter
    liftWGPrefix (setKeypair id {k with sendingCounter := k.sendingCounter + 1})
    if ← liftWGPrefix (branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES) then
      return ← outNokey true
    packetsCb := packetsCb ++ [{peer := pid, keypair := id, nonce, plaintext := pkt, ds}]
  _ ← liftWGPrefix (branch .stagedNonceIterate false)
  liftWGPrefix (peerGet (← liftWGPrefix (IndexOwner.peerDeref (.keypair id))))
  let allocation ← captureWGRun (packetsCb.mapM newTxSkb)
  emitStatePrefix {peer := pid, slot := id, keyRead, clockRead, packets := packetsCb, allocation}
  liftWGPrefix (createData pid allocation.value)

/-- All-input erasure preserves both original success endpoints and the exact Stop. -/
theorem stagingObserved_erases (pid : PeerId) :
    ErasesStatePrefix (stagingObserved pid) (sendStagedPackets pid) := by
  have emit_erase {α : Type} (e : TxAdmission) (a : WG.M α) :
      ErasesStatePrefix (do emitStatePrefix e; liftWGPrefix a) a := by
    intro w ambient h
    change (runStatePrefix (do emitStatePrefix e; liftWGPrefix a) w ambient h).1 = _
    simp only [runStatePrefix_bind, runStatePrefix_emit, liftWGPrefix, runStatePrefix_lift]
  unfold stagingObserved sendStagedPackets
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro p
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro empty
  split
  · exact erasesStatePrefix_pure _
  · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro _
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro kp
    have hout (invalid : Bool) := erasesStatePrefix_lift (E := TxAdmission)
      (Lifetimes.stagedOutNokey pid p.staged kp invalid)
    change ErasesStatePrefix
      (do
        if ← liftWGPrefix (branch .stagedNoKeypair kp.isNone) then return ← liftWGPrefix (Lifetimes.stagedOutNokey pid p.staged kp false)
        _) _
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro missing
    split
    · exact hout false
    · cases kp with
      | none => exact erasesStatePrefix_lift _
      | some id =>
        apply captureWGRun_bind_erases
        intro keyRead
        apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
        intro invalid
        split
        · exact hout false
        · simp only [branchExpired, birthdateTest, bind_assoc, pure_bind]
          apply captureWGRun_bind_erases
          intro clockRead
          apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
          intro expired
          split
          · exact hout true
          · repeat' first
              | exact emit_erase _ _
              | exact erasesStatePrefix_lift _
              | with_reducible exact erasesStatePrefix_pure _
              | exact hout true
              | with_reducible apply captureWGRun_bind_erases
              | with_reducible apply erasesStatePrefix_forIn
              | with_reducible apply erasesStatePrefix_bind
              | split
              | (with_reducible intro x; try dsimp only)
            all_goals first
              | (solve | simp_all)
              | (simp_all only [Option.some.injEq]; exact hout true)

def admissionsGood (h : List TxAdmission) : Prop := ∀ a ∈ h, a.Valid

variable {S T : Type}

def keep (C : Prop) (h : List TxAdmission) (_ : S) : Prop := admissionsGood h ∧ C

theorem lift_keep (a : StateT S (Except Stop) α) (C : Prop) :
    PrefixEnsures (keep C) admissionsGood (liftPrefix a) (fun _ => keep C) :=
  PrefixEnsures.lift a (fun _ _ hi => hi.1) (fun _ _ _ _ hi _ => hi)

theorem lift_forget (a : StateT S (Except Stop) α) (C : Prop) :
    PrefixEnsures (keep C) admissionsGood (liftPrefix a) (fun _ => keep True) :=
  (lift_keep a C).consequence (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, trivial⟩)

theorem pure_forget (x : α) (C : Prop) :
    PrefixEnsures (keep (S := S) C) admissionsGood (pure x) (fun _ => keep True) :=
  PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => ⟨hi.1, trivial⟩)

theorem capture_keep (a : StateT S (Except Stop) α) (C : Prop) :
    PrefixEnsures (keep C) admissionsGood (captureRun a)
      (fun r => keep (C ∧ r.Valid a)) := by
  apply PrefixEnsures.captureRun _ (fun _ _ hi => hi.1)
  intro h w x v hi hr
  exact ⟨hi.1, hi.2, hr⟩

theorem branch_keep (d : Decision) (b : Bool) (C : Prop) :
    PrefixEnsures (keep C) admissionsGood (liftPrefix (branch d b : Leanux.M Bool))
      (fun x => keep (C ∧ x = b)) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
  intro h w x v hi hr
  cases hr
  exact ⟨hi.1, hi.2, rfl⟩

theorem comparison_keep (d : Decision) (b : Bool) (left right : Int) (C : Prop) :
    PrefixEnsures (keep C) admissionsGood (liftPrefix (branchCmp d b left right : Leanux.M Bool))
      (fun x => keep (C ∧ x = b)) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
  intro h w x v hi hr
  cases hr
  exact ⟨hi.1, hi.2, rfl⟩

theorem lift_state_keep (a : StateT S (StateT T (Except Stop)) α) (C : Prop) :
    StatePrefixEnsures (fun h s _ => keep C h s) admissionsGood (liftStatePrefix a)
      (fun _ h s _ => keep C h s) :=
  fun s => lift_keep (a.run s) C

theorem lift_state_forget (a : StateT S (StateT T (Except Stop)) α) (C : Prop) :
    StatePrefixEnsures (fun h s _ => keep C h s) admissionsGood (liftStatePrefix a)
      (fun _ h s _ => keep True h s) :=
  fun s => lift_forget (a.run s) C

theorem pure_state_forget (x : α) (C : Prop) :
    StatePrefixEnsures (fun h (s : S) (_ : T) => keep C h s) admissionsGood (pure x)
      (fun _ h s _ => keep True h s) :=
  fun s => pure_forget (x, s) C

theorem capture_wg_keep (a : WG.M α) (C : Prop) :
    StatePrefixEnsures (fun h s _ => keep C h s) admissionsGood (captureWGRun a)
      (fun r h s _ => keep (C ∧ r.Valid a) h s) := by
  apply StatePrefixEnsures.captureWGRun _ (fun _ _ _ hi => hi.1)
  intro h w ambient x v ambient' hi hr
  exact ⟨hi.1, hi.2, hr⟩

theorem branch_state_keep (d : Decision) (b : Bool) (C : Prop) :
    StatePrefixEnsures (fun h s _ => keep C h s) admissionsGood (liftWGPrefix (branch d b))
      (fun x h s _ => keep (C ∧ x = b) h s) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
  intro h w ambient x v ambient' hi hr
  cases hr
  exact ⟨hi.1, hi.2, rfl⟩

theorem comparison_state_keep (d : Decision) (b : Bool) (left right : Int) (C : Prop) :
    StatePrefixEnsures (fun h s _ => keep C h s) admissionsGood (liftWGPrefix (branchCmp d b left right))
      (fun x h s _ => keep (C ∧ x = b) h s) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
  intro h w ambient x v ambient' hi hr
  cases hr
  exact ⟨hi.1, hi.2, rfl⟩

def batchBounds (pid : PeerId) (id : KeypairId) (ps : List DataPacket) : Prop :=
  ∀ p ∈ ps, p.peer = pid ∧ p.keypair = id ∧ p.nonce < REJECT_AFTER_MESSAGES

def gateFacts (id : KeypairId) (keyRead : WGRunWitness Keypair) (clockRead : WGRunWitness Int64) : Prop :=
  keyRead.Valid (getKeypair id) ∧ keyRead.value.sending.isValid = true ∧
  clockRead.Valid (hiddenClock64 .birthdateExpired) ∧
  ¬ deadline keyRead.value.sending.birthdate REJECT_AFTER_TIME ≤ clockRead.value

theorem emit_valid (a : TxAdmission) (C : Prop) (hv : C → a.Valid) :
    PrefixEnsures (keep (S := S) C) admissionsGood (emitPrefix a) (fun _ => keep True) := by
  intro w h hi
  have good : admissionsGood (h ++ [a]) := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hi.1 e he
    · have : e = a := by simpa using he
      subst e
      exact hv hi.2
  exact ⟨[a], by simp, by simpa using good, by simpa [keep] using good⟩

theorem emit_state_valid (a : TxAdmission) (C : Prop) (hv : C → a.Valid) :
    StatePrefixEnsures (fun h (s : S) (_ : T) => keep C h s) admissionsGood (emitStatePrefix a)
      (fun _ h s _ => keep True h s) := by
  intro s t h hi
  exact emit_valid (S := T) a C hv t h hi

/-- Every emitted batch has the original successful getter/clock/allocation
executions and the source admission guards, even if submission later stops. -/
theorem stagingObserved_safe (pid : PeerId) :
    StatePrefixEnsures (fun h s _ => keep True h s) admissionsGood (stagingObserved pid) (fun _ h s _ => keep True h s) := by
  unfold stagingObserved
  apply StatePrefixEnsures.bind (lift_state_keep _ True)
  intro p
  apply StatePrefixEnsures.bind (lift_state_keep _ True)
  intro empty
  split
  · exact pure_state_forget _ _
  · apply StatePrefixEnsures.bind (lift_state_keep _ True)
    intro _
    apply StatePrefixEnsures.bind (lift_state_keep _ True)
    intro kp
    apply StatePrefixEnsures.bind (lift_state_keep _ True)
    intro missing
    split
    · exact lift_state_forget _ _
    · cases kp with
      | none => exact lift_state_forget _ _
      | some id =>
        apply StatePrefixEnsures.bind (capture_wg_keep _ True)
        intro keyRead
        apply StatePrefixEnsures.bind (branch_state_keep _ _ _)
        intro invalid
        cases invalid with
        | true => exact lift_state_forget _ _
        | false =>
          apply StatePrefixEnsures.bind (capture_wg_keep _ _)
          intro clockRead
          apply StatePrefixEnsures.bind (comparison_state_keep _ _ _ _ _)
          intro expired
          cases expired with
          | true => exact lift_state_forget _ _
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            apply StatePrefixEnsures.consequence
              (P := fun h s _ => keep (gateFacts id keyRead clockRead ∧ batchBounds pid id []) h s)
              (Q := fun _ h s _ => keep True h s)
            · apply StatePrefixEnsures.bind (Q := fun acc : Option Unit × List DataPacket =>
                  fun h s _ => keep (gateFacts id keyRead clockRead ∧ batchBounds pid id acc.2) h s)
              · apply StatePrefixEnsures.forInInvariant p.staged (none, []) _
                  (fun acc : Option Unit × List DataPacket =>
                    fun h s _ => keep (gateFacts id keyRead clockRead ∧ batchBounds pid id acc.2) h s) admissionsGood
                  (fun _ _ _ _ hi => hi.1)
                intro pkt acc
                apply StatePrefixEnsures.bind (lift_state_keep _ _)
                intro _
                apply StatePrefixEnsures.bind (lift_state_keep _ _)
                intro ds
                apply StatePrefixEnsures.bind (lift_state_keep _ _)
                intro fresh
                apply StatePrefixEnsures.bind (lift_state_keep _ _)
                intro _
                apply StatePrefixEnsures.bind (comparison_state_keep _ _ _ _ _)
                intro rejected
                cases rejected with
                | true =>
                  apply StatePrefixEnsures.bind (lift_state_keep _ _)
                  intro result
                  apply StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1)
                  intro h w ambient hi
                  exact ⟨hi.1, hi.2.1⟩
                | false =>
                  apply StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.1)
                  intro h w ambient hi
                  refine ⟨hi.1, hi.2.1.1, ?_⟩
                  intro q hq
                  rcases List.mem_append.mp hq with old | new
                  · exact hi.2.1.2 q old
                  · have he : q = DataPacket.mk pid id fresh.sendingCounter pkt ds .uncrypted [] := by simpa using new
                    subst q
                    refine ⟨rfl, rfl, ?_⟩
                    have hn : ¬ fresh.sendingCounter ≥ REJECT_AFTER_MESSAGES := by
                      simpa using hi.2.2.symm
                    change fresh.sendingCounter < REJECT_AFTER_MESSAGES
                    omega
              · intro acc
                rcases acc with ⟨done, ps⟩
                cases done with
                | some result => exact pure_state_forget _ _
                | none =>
                  apply StatePrefixEnsures.bind (lift_state_keep _ _)
                  intro _
                  apply StatePrefixEnsures.bind (lift_state_keep _ _)
                  intro fresh
                  apply StatePrefixEnsures.bind (lift_state_keep _ _)
                  intro _
                  apply StatePrefixEnsures.bind (capture_wg_keep _ _)
                  intro allocation
                  apply StatePrefixEnsures.bind
                  · apply emit_state_valid
                    intro hi
                    exact ⟨hi.1.1.1, hi.1.1.2.1, hi.1.1.2.2.1,
                      hi.1.1.2.2.2, hi.1.2, hi.2⟩
                  · intro _
                    exact lift_state_forget _ _
            · intro h w ambient hi
              refine ⟨hi.1, ?_, ?_⟩
              · refine ⟨hi.2.1.1.1.2, ?_, hi.2.1.2, ?_⟩
                · simpa using hi.2.1.1.2.symm
                · simpa using hi.2.2.symm
              · simp [batchBounds]
            · intro _ _ _ _ hi
              exact hi

end Leanux.Proofs.WG.KeyTimes
