import Leanux.Proofs.WG.TransmitSecurity.WireNonce
import Leanux.Proofs.Logged.NativeCapture

/-! The native encryption call split immediately before its key read and AEAD.
All allocation and checksum refusals remain on their original branches. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Encryption
open Leanux Leanux.WG Leanux.Proofs.Logged

structure Prepared where
  inner : Packet
  padding : Nat

def prepare (checksum : Packet → Leanux.M Packet) (pkt : DataPacket) :
    Leanux.M (Option Prepared) := do
  skipCut [.flowHashSecret]
  let padding ← calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu
  if ← branch .encCowHeadFailed !(← hiddenAlloc .skbCowHead) then return none
  let mut inner := pkt.plaintext
  if ← branch .encChecksumPartial inner.csum.isSome then
    if ← branch .encChecksumHelpFailed !(← hiddenAlloc .skbChecksumHelp) then return none
    inner ← checksum inner
  let cowOk ← hiddenAlloc .skbCowDataTx
  if ← branch .encCowDataFailed !cowOk then return none
  if ← branch .encTooManyFrags false then return none
  return some ⟨inner,padding⟩

def finish (slot : KeypairId) (pkt : DataPacket) (prepared : Option Prepared) :
    Leanux.M (Option (List UInt8)) := do
  let some p := prepared | return none
  let k ← getKeypair slot
  if ← branch .encSgvecFailed false then return none
  return some (dataMessage k.remoteIndex pkt.nonce k.sending.key
    (p.inner.bytes ++ List.replicate p.padding 0))

private theorem bind_congr (a : Leanux.M α) (f g : α → Leanux.M β)
    (same : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
  congrArg (fun k => a >>= k) (funext same)
private theorem if_bind (p : Prop) [Decidable p] (a b : Leanux.M α)
    (f : α → Leanux.M β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split <;> rfl

theorem factor (checksum : Packet → Leanux.M Packet) (slot : KeypairId) (pkt : DataPacket) :
    encryptPacket checksum slot pkt = (prepare checksum pkt >>= finish slot pkt) := by
  unfold encryptPacket prepare
  simp only [bind_assoc, if_bind, pure_bind]
  repeat' first
    | rfl
    | with_reducible apply bind_congr
    | intro x
    | split
    | (simp_all only [bind_assoc, if_bind, pure_bind, finish, ↓reduceIte]; rfl)
  all_goals rfl

structure Receipt where
  slot : KeypairId
  packet : DataPacket
  prepared : Prepared
  preparation : RunWitness (Option Prepared)
  keyRead : RunWitness Keypair

def Receipt.ciphertext (r : Receipt) : List UInt8 :=
  dataMessage r.keyRead.value.remoteIndex r.packet.nonce r.keyRead.value.sending.key
    (r.prepared.inner.bytes ++ List.replicate r.prepared.padding 0)

def Receipt.Valid (checksum : Packet → Leanux.M Packet) (r : Receipt) : Prop :=
  r.preparation.Valid (prepare checksum r.packet) ∧
  r.preparation.value = some r.prepared ∧
  r.preparation.after = r.keyRead.before ∧
  r.keyRead.Valid (liftWG (getKeypair r.slot))

def observe (checksum : Packet → Leanux.M Packet) (slot : KeypairId) (pkt : DataPacket) :
    PrefixM Receipt (Option (List UInt8)) := do
  let preparation ← captureRun (prepare checksum pkt)
  let some p := preparation.value | return none
  let keyRead ← captureRun (liftWG (getKeypair slot))
  if ← liftPrefix (branch .encSgvecFailed false) then return none
  let receipt : Receipt := ⟨slot,pkt,p,preparation,keyRead⟩
  emitPrefix receipt
  return some receipt.ciphertext

theorem observe_erases (checksum : Packet → Leanux.M Packet) (slot : KeypairId) (pkt : DataPacket) :
    ErasesPrefix (observe checksum slot pkt) (encryptPacket checksum slot pkt) := by
  rw [factor]
  unfold observe
  apply captureRun_bind_erases
  intro preparation
  cases hp : preparation.value with
  | none => exact erasesPrefix_pure _
  | some p =>
    unfold finish
    dsimp only
    apply captureRun_bind_erases
    intro keyRead
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro failed
    split
    · exact erasesPrefix_pure _
    · intro w h
      simp only [runPrefix_bind,runPrefix_emit,runPrefix_pure]
      rfl

end Leanux.Proofs.WG.TransmitSecurity.Encryption
