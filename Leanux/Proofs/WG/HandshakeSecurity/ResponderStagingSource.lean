import Leanux.Proofs.WG.HandshakeSecurity.ResponderFrames
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationSource

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- The original staging prefix through its current-key borrow, before any
key-validity, age or nonce guard. Empty staged queues return no selection. -/
def selectionPrefix (pid : PeerId) : WG.M (Option (Peer × Option KeypairId)) := do
  let p ← getPeer pid
  if ← branch .stagedEmpty p.staged.isEmpty then return none
  setPeer pid {p with staged := []}
  let kp ← keypairGet p.keypairCurrent
  return some (p, kp)

def selectionTail (pid : PeerId) : Option (Peer × Option KeypairId) → WG.M Unit
  | none => pure ()
  | some (p, keypair) => do
    let packets := p.staged
    let outNokey := Lifetimes.stagedOutNokey pid packets keypair
    if ← branch .stagedNoKeypair keypair.isNone then return ← outNokey false
    let some id := keypair | invariant "unreachable"
    let k ← getKeypair id
    if ← branch .stagedKeyInvalid !k.sending.isValid then return ← outNokey false
    if ← branchExpired .stagedBirthdateExpired k.sending.birthdate REJECT_AFTER_TIME then
      return ← outNokey true
    let mut packetsCb : List DataPacket := []
    for pkt in packets do
      _ ← branch .stagedNonceIterate true
      let ds ← ipTunnelEcnEncap pkt
      let k ← getKeypair id
      let nonce := k.sendingCounter
      setKeypair id { k with sendingCounter := k.sendingCounter + 1 }
      if ← branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES then return ← outNokey true
      packetsCb := packetsCb ++ [{ peer := pid, keypair := id, nonce, plaintext := pkt, ds }]
    _ ← branch .stagedNonceIterate false
    peerGet (← IndexOwner.peerDeref (.keypair id))
    let item ← packetsCb.mapM newTxSkb
    createData pid item

theorem selection_factor (pid : PeerId) :
    sendStagedPackets pid = selectionPrefix pid >>= selectionTail pid := by
  unfold sendStagedPackets selectionPrefix
  simp only [bind_assoc, Queues.RxCredits.bind_if_source, pure_bind]
  congr 1

end Leanux.Proofs.WG.HandshakeSecurity.Responder
