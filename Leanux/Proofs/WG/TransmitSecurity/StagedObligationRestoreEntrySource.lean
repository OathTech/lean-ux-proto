import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationRestoreCore
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationTakeSource
import Leanux.Proofs.WG.TransmitSecurity.NonceSource

/-! Source cuts before restoring a selected batch. These factors retain the
original branch order and nonce loop; their callbacks are the original no-key
and submission expressions, rather than an abstract sequence of frames. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.RestoreEntry
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
open HandshakeSecurity.StagedConservation

def prefixWith [Monad m] (step : {α : Type} → WG.M α → m α)
    (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) : m Unit := do
  if invalid then
    let some id := keypair | step (invariant "unreachable")
    let k ← step (getKeypair id)
    step (setKeypair id {k with sending := {k.sending with isValid := false}})
  step (keypairPut keypair false)
  for _ in packets do _ ← step (branch .stagedOrphanWalk true)
  _ ← step (branch .stagedOrphanWalk false)

theorem no_key_factor [Monad m] [LawfulMonad m] (o : TimerEffects.Ops m)
    (restore : PeerId → List Packet → m Unit) (queue : PeerId → Bool → m Unit)
    (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    Restore.noKeyWith o restore queue pid packets keypair invalid = (do
      prefixWith o.step packets keypair invalid
      restore pid packets
      queue pid false) := by
  cases invalid <;> cases keypair <;>
    simp only [Restore.noKeyWith,prefixWith,Bool.false_eq_true,ite_false,ite_true,
      bind_assoc,pure_bind]

def checkedWith [Monad m] (step : {α : Type} → WG.M α → m α)
    (reserve : KeypairId → m Nat)
    (noKey : Option KeypairId → Bool → m Unit)
    (submit : KeypairId → List DataPacket → m Unit)
    (pid : PeerId) (peer : Peer) (keypair : Option KeypairId) : m Unit := do
  if ← step (branch .stagedNoKeypair keypair.isNone) then return ← noKey keypair false
  let some id := keypair | step (invariant "unreachable")
  let k ← step (getKeypair id)
  if ← step (branch .stagedKeyInvalid !k.sending.isValid) then return ← noKey keypair false
  if ← step (branchExpired .stagedBirthdateExpired k.sending.birthdate REJECT_AFTER_TIME) then
    return ← noKey keypair true
  let mut packetsCb : List DataPacket := []
  for pkt in peer.staged do
    _ ← step (branch .stagedNonceIterate true)
    let ds ← step (ipTunnelEcnEncap pkt)
    let nonce ← reserve id
    if ← step (branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES) then
      return ← noKey keypair true
    packetsCb := packetsCb ++ [{peer := pid,keypair := id,nonce,plaintext := pkt,ds}]
  _ ← step (branch .stagedNonceIterate false)
  submit id packetsCb

def submitNative (pid : PeerId) (kid : KeypairId) (packets : List DataPacket) : WG.M Unit := do
  peerGet (← IndexOwner.peerDeref (.keypair kid))
  let items ← packets.mapM newTxSkb
  createData pid items

/-- The checked continuation is exactly the original source after the selected
peer/current-key read. Early no-key and nonce rejection use the same callbacks. -/
theorem checked_native (pid : PeerId) (peer : Peer) (keypair : Option KeypairId) :
    checkedWith (fun action => action) Nonce.reserveNative
      (Lifetimes.stagedOutNokey pid peer.staged) (submitNative pid) pid peer keypair =
      HandshakeSecurity.Responder.selectionTail pid (some (peer,keypair)) := by
  cases keypair <;>
    simp only [checkedWith,Nonce.reserveNative,submitNative,
      HandshakeSecurity.Responder.selectionTail,bind_assoc,pure_bind]

/-- The full source uses the existing original selection prefix and this
checked continuation. The later restore-entry contracts need no completed
enclosing send to identify their native callback position. -/
theorem staging_native (pid : PeerId) :
    sendStagedPackets pid = (do
      let selected ← HandshakeSecurity.Responder.selectionPrefix pid
      match selected with
      | none => pure ()
      | some (peer,keypair) =>
        checkedWith (fun action => action) Nonce.reserveNative
          (Lifetimes.stagedOutNokey pid peer.staged) (submitNative pid) pid peer keypair) := by
  rw [HandshakeSecurity.Responder.selection_factor]
  congr 1
  funext selected
  cases selected with
  | none => rfl
  | some pair => exact (checked_native pid pair.1 pair.2).symm

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.RestoreEntry
