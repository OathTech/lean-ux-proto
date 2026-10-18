import Leanux.Proofs.WG.TransmitSecurity.NonceSource
import Leanux.Proofs.WG.Lifetimes.TxStaging

/-! The complete native staged-send control flow, observing each allocated
nonce before its bound check. Failed and restored batches retain their prefix. -/
set_option maxHeartbeats 600000

namespace Leanux.Proofs.WG.TransmitSecurity.Nonce
open Leanux Leanux.WG Leanux.Proofs.Logged

def stagingObserved (pid : PeerId) : WGPrefix Allocation Unit := do
  let p ← liftWGPrefix (getPeer pid)
  if ← liftWGPrefix (branch .stagedEmpty p.staged.isEmpty) then return
  let packets := p.staged
  liftWGPrefix (setPeer pid { p with staged := [] })
  let keypair ← liftWGPrefix (keypairGet p.keypairCurrent)
  let outNokey (invalid : Bool) := liftWGPrefix (Lifetimes.stagedOutNokey pid packets keypair invalid)
  if ← liftWGPrefix (branch .stagedNoKeypair keypair.isNone) then return ← outNokey false
  let some id := keypair | liftWGPrefix (invariant "unreachable")
  let k ← liftWGPrefix (getKeypair id)
  if ← liftWGPrefix (branch .stagedKeyInvalid !k.sending.isValid) then return ← outNokey false
  if ← liftWGPrefix (branchExpired .stagedBirthdateExpired k.sending.birthdate REJECT_AFTER_TIME) then
    return ← outNokey true
  let mut packetsCb : List DataPacket := []
  for pkt in packets do
    _ ← liftWGPrefix (branch .stagedNonceIterate true)
    let ds ← liftWGPrefix (ipTunnelEcnEncap pkt)
    let nonce ← reserveObserved id
    if ← liftWGPrefix (branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES) then return ← outNokey true
    packetsCb := packetsCb ++ [{ peer := pid, keypair := id, nonce, plaintext := pkt, ds }]
  _ ← liftWGPrefix (branch .stagedNonceIterate false)
  liftWGPrefix (peerGet (← liftWGPrefix (IndexOwner.peerDeref (.keypair id))))
  let item ← liftWGPrefix (packetsCb.mapM newTxSkb)
  liftWGPrefix (createData pid item)

theorem stagingObserved_erases (pid : PeerId) :
    ErasesStatePrefix (stagingObserved pid) (sendStagedPackets pid) := by
  have emitThen {α : Type} (e : Allocation) (g : WGPrefix Allocation α) (a : WG.M α)
      (hg : ErasesStatePrefix g a) :
      ErasesStatePrefix (do emitStatePrefix e; g) a := by
    intro w ambient h
    change (runStatePrefix (do emitStatePrefix e; g) w ambient h).1 = _
    rw [runStatePrefix_bind, runStatePrefix_emit]
    exact hg w ambient (h ++ [e])
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
    have hout (invalid : Bool) := erasesStatePrefix_lift (E := Allocation)
      (Lifetimes.stagedOutNokey pid p.staged kp invalid)
    change ErasesStatePrefix
      (do
        if ← liftWGPrefix (branch .stagedNoKeypair kp.isNone) then
          return ← liftWGPrefix (Lifetimes.stagedOutNokey pid p.staged kp false)
        _) _
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro missing
    split
    · exact hout false
    · cases kp with
      | none => exact erasesStatePrefix_lift _
      | some id =>
        apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
        intro k
        apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
        intro invalid
        split
        · exact hout false
        · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
          intro expired
          split
          · exact hout true
          · simp only [reserveObserved, bind_assoc, pure_bind]
            repeat' first
              | exact erasesStatePrefix_lift _
              | with_reducible exact erasesStatePrefix_pure _
              | exact hout true
              | with_reducible apply emitThen
              | with_reducible apply erasesStatePrefix_forIn
              | with_reducible apply erasesStatePrefix_bind
              | split
              | (with_reducible intro x; try dsimp only)
            all_goals first
              | (solve | simp_all)
              | (simp_all only [Option.some.injEq]; exact hout true)

end Leanux.Proofs.WG.TransmitSecurity.Nonce
