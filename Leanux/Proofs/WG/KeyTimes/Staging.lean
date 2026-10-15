import Leanux.Proofs.Logged.Capture
import Leanux.Proofs.WG.KeyTimes.Receive
import Leanux.Proofs.WG.Lifetimes.TxStaging

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! One original staging call, observed at the completed allocation / submit
boundary. Captured Worlds are proof-side execution witnesses only. -/
namespace Leanux.Proofs.WG.KeyTimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.CounterWindow

structure TxAdmission where
  peer : PeerId
  slot : KeypairId
  keyRead : RunWitness Keypair
  clockRead : RunWitness Int64
  packets : List DataPacket
  allocation : RunWitness (List SkbId)

def TxAdmission.Valid (a : TxAdmission) : Prop :=
  a.keyRead.Valid (getKeypair a.slot) ∧
  a.keyRead.value.sending.isValid = true ∧
  a.clockRead.Valid (hiddenClock64 .birthdateExpired) ∧
  ¬ deadline a.keyRead.value.sending.birthdate REJECT_AFTER_TIME ≤ a.clockRead.value ∧
  (∀ p ∈ a.packets, p.peer = a.peer ∧ p.keypair = a.slot ∧ p.nonce < REJECT_AFTER_MESSAGES) ∧
  a.allocation.Valid (a.packets.mapM newTxSkb)

def stagingObserved (pid : PeerId) : PrefixM TxAdmission Unit := do
  let p ← liftPrefix (getPeer pid)
  if ← liftPrefix (branch .stagedEmpty p.staged.isEmpty) then return
  let packets := p.staged
  liftPrefix (setPeer pid {p with staged := []})
  let keypair ← liftPrefix (keypairGet p.keypairCurrent)
  let outNokey (invalid : Bool) := liftPrefix (Lifetimes.stagedOutNokey pid packets keypair invalid)
  if ← liftPrefix (branch .stagedNoKeypair keypair.isNone) then return ← outNokey false
  let some id := keypair | liftPrefix (invariant "unreachable")
  let keyRead ← captureRun (getKeypair id)
  let k := keyRead.value
  if ← liftPrefix (branch .stagedKeyInvalid !k.sending.isValid) then return ← outNokey false
  let clockRead ← captureRun (hiddenClock64 .birthdateExpired)
  let lhs := deadline k.sending.birthdate REJECT_AFTER_TIME
  if ← liftPrefix (branchCmp .stagedBirthdateExpired (lhs ≤ clockRead.value) lhs.toInt clockRead.value.toInt) then
    return ← outNokey true
  let mut packetsCb : List DataPacket := []
  for pkt in packets do
    _ ← liftPrefix (branch .stagedNonceIterate true)
    let ds ← liftPrefix (ipTunnelEcnEncap pkt)
    let k ← liftPrefix (getKeypair id)
    let nonce := k.sendingCounter
    liftPrefix (setKeypair id {k with sendingCounter := k.sendingCounter + 1})
    if ← liftPrefix (branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES) then
      return ← outNokey true
    packetsCb := packetsCb ++ [{peer := pid, keypair := id, nonce, plaintext := pkt, ds}]
  _ ← liftPrefix (branch .stagedNonceIterate false)
  liftPrefix (peerGet (← liftPrefix (IndexOwner.peerDeref (.keypair id))))
  let allocation ← captureRun (packetsCb.mapM newTxSkb)
  emitPrefix {peer := pid, slot := id, keyRead, clockRead, packets := packetsCb, allocation}
  liftPrefix (createData pid allocation.value)

/-- All-input erasure preserves the original complete success World and exact Stop. -/
theorem stagingObserved_erases (pid : PeerId) :
    ErasesPrefix (stagingObserved pid) (sendStagedPackets pid) := by
  unfold stagingObserved sendStagedPackets
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro p
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro empty
  split
  · exact erasesPrefix_pure _
  · apply erasesPrefix_bind (erasesPrefix_lift _)
    intro _
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro kp
    have hout (invalid : Bool) := erasesPrefix_lift (Event := TxAdmission)
      (Lifetimes.stagedOutNokey pid p.staged kp invalid)
    change ErasesPrefix
      (do
        if ← liftPrefix (branch .stagedNoKeypair kp.isNone) then return ← liftPrefix (Lifetimes.stagedOutNokey pid p.staged kp false)
        _) _
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro missing
    split
    · exact hout false
    · cases kp with
      | none => exact erasesPrefix_lift _
      | some id =>
        apply captureRun_bind_erases
        intro keyRead
        apply erasesPrefix_bind (erasesPrefix_lift _)
        intro invalid
        split
        · exact hout false
        · simp only [branchExpired, birthdateTest, bind_assoc, pure_bind]
          apply captureRun_bind_erases
          intro clockRead
          apply erasesPrefix_bind (erasesPrefix_lift _)
          intro expired
          split
          · exact hout true
          · repeat' first
              | with_reducible exact emitThen_erases _ _
              | with_reducible exact erasesPrefix_lift _
              | with_reducible exact erasesPrefix_pure _
              | exact hout true
              | with_reducible apply captureRun_bind_erases
              | with_reducible apply erasesPrefix_forIn
              | with_reducible apply erasesPrefix_bind
              | split
              | (with_reducible intro x; try dsimp only)
            all_goals first
              | (solve | simp_all)
              | (simp_all only [Option.some.injEq]; exact hout true)

def admissionsGood (h : List TxAdmission) : Prop := ∀ a ∈ h, a.Valid

def keep (C : Prop) (h : List TxAdmission) (_ : World) : Prop := admissionsGood h ∧ C

theorem lift_keep (a : M α) (C : Prop) :
    PrefixEnsures (keep C) admissionsGood (liftPrefix a) (fun _ => keep C) :=
  PrefixEnsures.lift a (fun _ _ hi => hi.1) (fun _ _ _ _ hi _ => hi)

theorem lift_forget (a : M α) (C : Prop) :
    PrefixEnsures (keep C) admissionsGood (liftPrefix a) (fun _ => keep True) :=
  (lift_keep a C).consequence (fun _ _ hi => hi) (fun _ _ _ hi => ⟨hi.1, trivial⟩)

theorem pure_forget (x : α) (C : Prop) :
    PrefixEnsures (keep C) admissionsGood (pure x) (fun _ => keep True) :=
  PrefixEnsures.pure (fun _ _ hi => hi.1) (fun _ _ hi => ⟨hi.1, trivial⟩)

theorem capture_keep (a : M α) (C : Prop) :
    PrefixEnsures (keep C) admissionsGood (captureRun a)
      (fun r => keep (C ∧ r.Valid a)) := by
  apply PrefixEnsures.captureRun _ (fun _ _ hi => hi.1)
  intro h w x v hi hr
  exact ⟨hi.1, hi.2, hr⟩

theorem branch_keep (d : Decision) (b : Bool) (C : Prop) :
    PrefixEnsures (keep C) admissionsGood (liftPrefix (branch d b))
      (fun x => keep (C ∧ x = b)) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
  intro h w x v hi hr
  cases hr
  exact ⟨hi.1, hi.2, rfl⟩

theorem comparison_keep (d : Decision) (b : Bool) (left right : Int) (C : Prop) :
    PrefixEnsures (keep C) admissionsGood (liftPrefix (branchCmp d b left right))
      (fun x => keep (C ∧ x = b)) := by
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.1)
  intro h w x v hi hr
  cases hr
  exact ⟨hi.1, hi.2, rfl⟩

def batchBounds (pid : PeerId) (id : KeypairId) (ps : List DataPacket) : Prop :=
  ∀ p ∈ ps, p.peer = pid ∧ p.keypair = id ∧ p.nonce < REJECT_AFTER_MESSAGES

def gateFacts (id : KeypairId) (keyRead : RunWitness Keypair) (clockRead : RunWitness Int64) : Prop :=
  keyRead.Valid (getKeypair id) ∧ keyRead.value.sending.isValid = true ∧
  clockRead.Valid (hiddenClock64 .birthdateExpired) ∧
  ¬ deadline keyRead.value.sending.birthdate REJECT_AFTER_TIME ≤ clockRead.value

theorem emit_valid (a : TxAdmission) (C : Prop) (hv : C → a.Valid) :
    PrefixEnsures (keep C) admissionsGood (emitPrefix a) (fun _ => keep True) := by
  intro w h hi
  have good : admissionsGood (h ++ [a]) := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hi.1 e he
    · have : e = a := by simpa using he
      subst e
      exact hv hi.2
  exact ⟨[a], by simp, by simpa using good, by simpa [keep] using good⟩

/-- Every emitted batch has the original successful getter/clock/allocation
executions and the source admission guards, even if submission later stops. -/
theorem stagingObserved_safe (pid : PeerId) :
    PrefixEnsures (keep True) admissionsGood (stagingObserved pid) (fun _ => keep True) := by
  unfold stagingObserved
  apply PrefixEnsures.bind (lift_keep _ True)
  intro p
  apply PrefixEnsures.bind (lift_keep _ True)
  intro empty
  split
  · exact pure_forget _ _
  · apply PrefixEnsures.bind (lift_keep _ True)
    intro _
    apply PrefixEnsures.bind (lift_keep _ True)
    intro kp
    apply PrefixEnsures.bind (lift_keep _ True)
    intro missing
    split
    · exact lift_forget _ _
    · cases kp with
      | none => exact lift_forget _ _
      | some id =>
        apply PrefixEnsures.bind (capture_keep _ True)
        intro keyRead
        apply PrefixEnsures.bind (branch_keep _ _ _)
        intro invalid
        cases invalid with
        | true => exact lift_forget _ _
        | false =>
          apply PrefixEnsures.bind (capture_keep _ _)
          intro clockRead
          apply PrefixEnsures.bind (comparison_keep _ _ _ _ _)
          intro expired
          cases expired with
          | true => exact lift_forget _ _
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            apply PrefixEnsures.consequence
              (P := keep (gateFacts id keyRead clockRead ∧ batchBounds pid id []))
              (Q := fun _ => keep True)
            · apply PrefixEnsures.bind (Q := fun acc : Option Unit × List DataPacket =>
                  keep (gateFacts id keyRead clockRead ∧ batchBounds pid id acc.2))
              · apply PrefixEnsures.forInInvariant p.staged (none, []) _
                  (fun acc : Option Unit × List DataPacket =>
                    keep (gateFacts id keyRead clockRead ∧ batchBounds pid id acc.2)) admissionsGood
                  (fun _ _ _ hi => hi.1)
                intro pkt acc
                apply PrefixEnsures.bind (lift_keep _ _)
                intro _
                apply PrefixEnsures.bind (lift_keep _ _)
                intro ds
                apply PrefixEnsures.bind (lift_keep _ _)
                intro fresh
                apply PrefixEnsures.bind (lift_keep _ _)
                intro _
                apply PrefixEnsures.bind (comparison_keep _ _ _ _ _)
                intro rejected
                cases rejected with
                | true =>
                  apply PrefixEnsures.bind (lift_keep _ _)
                  intro result
                  apply PrefixEnsures.pure (fun _ _ hi => hi.1)
                  intro h w hi
                  exact ⟨hi.1, hi.2.1⟩
                | false =>
                  apply PrefixEnsures.pure (fun _ _ hi => hi.1)
                  intro h w hi
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
                | some result => exact pure_forget _ _
                | none =>
                  apply PrefixEnsures.bind (lift_keep _ _)
                  intro _
                  apply PrefixEnsures.bind (lift_keep _ _)
                  intro fresh
                  apply PrefixEnsures.bind (lift_keep _ _)
                  intro _
                  apply PrefixEnsures.bind (capture_keep _ _)
                  intro allocation
                  apply PrefixEnsures.bind
                  · apply emit_valid
                    intro hi
                    exact ⟨hi.1.1.1, hi.1.1.2.1, hi.1.1.2.2.1,
                      hi.1.1.2.2.2, hi.1.2, hi.2⟩
                  · intro _
                    exact lift_forget _ _
            · intro h w hi
              refine ⟨hi.1, ?_, ?_⟩
              · refine ⟨hi.2.1.1.1.2, ?_, hi.2.1.2, ?_⟩
                · simpa using hi.2.1.1.2.symm
                · simpa using hi.2.2.symm
              · simp [batchBounds]
            · intro _ _ _ hi
              exact hi

end Leanux.Proofs.WG.KeyTimes
