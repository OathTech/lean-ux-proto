import Leanux.Proofs.WG.KeyTimes.Staging

namespace Leanux.Proofs.WG.HandshakeSecurity.StagingSelection
open Leanux Leanux.WG Leanux.Proofs.Logged
open KeyTimes

/-- Actual current-slot selection joined to the native admitted packet batch. -/
structure Receipt where
  peerRead : WGRunWitness Peer
  loanRead : WGRunWitness (Option KeypairId)
  admission : TxAdmission

def Receipt.Valid (r : Receipt) : Prop :=
  r.peerRead.Valid (getPeer r.admission.peer) ∧
  r.loanRead.Valid (keypairGet r.peerRead.value.keypairCurrent) ∧
  r.loanRead.value = some r.admission.slot ∧ r.admission.Valid

def afterSelection (pid : PeerId) (peerRead : WGRunWitness Peer)
    (loanRead : WGRunWitness (Option KeypairId)) : WGPrefix Receipt Unit := do
  let packets := peerRead.value.staged
  let keypair := loanRead.value
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
  emitStatePrefix {peerRead, loanRead, admission :=
    {peer := pid, slot := id, keyRead, clockRead, packets := packetsCb, allocation}}
  liftWGPrefix (createData pid allocation.value)

def observed (pid : PeerId) : WGPrefix Receipt Unit := do
  let peerRead ← captureWGRun (getPeer pid)
  let p := peerRead.value
  if ← liftWGPrefix (branch .stagedEmpty p.staged.isEmpty) then return
  liftWGPrefix (setPeer pid {p with staged := []})
  let loanRead ← captureWGRun (keypairGet p.keypairCurrent)
  afterSelection pid peerRead loanRead

/-- All-input erasure preserves both original success endpoints and the exact Stop. -/
theorem erases (pid : PeerId) :
    ErasesStatePrefix (observed pid) (sendStagedPackets pid) := by
  have emit_erase {α : Type} (e : Receipt) (a : WG.M α) :
      ErasesStatePrefix (do emitStatePrefix e; liftWGPrefix a) a := by
    intro w ambient h
    change (runStatePrefix (do emitStatePrefix e; liftWGPrefix a) w ambient h).1 = _
    simp only [runStatePrefix_bind, runStatePrefix_emit, liftWGPrefix, runStatePrefix_lift]
  unfold observed sendStagedPackets
  apply captureWGRun_bind_erases
  intro peerRead
  let p := peerRead.value
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro empty
  split
  · exact erasesStatePrefix_pure _
  · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro _
    apply captureWGRun_bind_erases
    intro loanRead
    unfold afterSelection
    have hout (invalid : Bool) := erasesStatePrefix_lift (E := Receipt)
      (Lifetimes.stagedOutNokey pid p.staged loanRead.value invalid)
    change ErasesStatePrefix
      (do
        if ← liftWGPrefix (branch .stagedNoKeypair loanRead.value.isNone) then return ← liftWGPrefix (Lifetimes.stagedOutNokey pid p.staged loanRead.value false)
        _) _
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro missing
    split
    · exact hout false
    · cases loanRead.value with
      | none => exact erasesStatePrefix_lift _
      | some id =>
        have hout (invalid : Bool) := erasesStatePrefix_lift (E := Receipt)
          (Lifetimes.stagedOutNokey pid peerRead.value.staged (some id) invalid)
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
          · apply erasesStatePrefix_bind
            · apply erasesStatePrefix_forIn
              intro pkt acc
              apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
              intro _
              apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
              intro ds
              apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
              intro k
              apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
              intro _
              apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
              intro rejected
              split
              · exact erasesStatePrefix_bind (hout true) (fun _ => erasesStatePrefix_pure _)
              · exact erasesStatePrefix_pure _
            · intro acc
              rcases acc with ⟨done, ps⟩
              cases done with
              | some result => exact erasesStatePrefix_pure _
              | none =>
                apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
                intro _
                apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
                intro owner
                apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
                intro _
                apply captureWGRun_bind_erases
                intro allocation
                exact emit_erase _ _

end Leanux.Proofs.WG.HandshakeSecurity.StagingSelection
