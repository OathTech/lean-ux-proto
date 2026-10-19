import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalPublication
import Leanux.Proofs.WG.TransmitSecurity.WorkerEncryption
import Leanux.Proofs.WG.AuthenticatedEffects.CausalFocusSource

/-! The original encryption worker with only its final publication exposed.
Its AEAD observer and source guards remain in place, including stopped walks. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.EncryptionSource
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity AuthenticatedEffects

structure Ops (E : Type) where
  step : {α : Type} → Leanux.M α → PrefixM E α
  head : SkbId → PrefixM E (RunWitness DataPacket)
  packet : SkbId → RunWitness DataPacket → SkbId → PrefixM E (Option (List UInt8))
  publish : List SkbId → PacketState → PrefixM E Unit

def native : Ops WorkerEncryption.Receipt where
  step := liftPrefix
  head := fun id => captureRun (liftWG (getTxSkb id))
  packet := WorkerEncryption.packet
  publish := fun item state => liftPrefix (liftWG (enqueuePerPeerTx item state))

def afterHead (o : Ops E) (first : List SkbId) (headId : SkbId) (head : RunWitness DataPacket) : PrefixM E Bool := do
  let mut state := PacketState.crypted
  for id in first do
    _ ← o.step (branch .encWorkerSkbIterate true)
    let encrypted ← o.packet headId head id
    if ← o.step (branch .encWorkerEncrypted encrypted.isSome) then
      o.step (liftWG (setTxSkb id fun p => {p with bytes := encrypted.getD []}))
    else
      state := .dead
      break
  if state == .crypted then _ ← o.step (branch .encWorkerSkbIterate false)
  o.publish first state
  return true

def tail (o : Ops E) (item : Option (List SkbId)) : PrefixM E Bool := do
  _ ← o.step (branch .encWorkerConsumed item.isSome)
  match item with
  | none => return false
  | some first =>
    let some headId := first.head? | o.step (invariant "an empty ring item")
    let head ← o.head headId
    afterHead o first headId head

theorem afterHead_native (first : List SkbId) (headId : SkbId) (head : RunWitness DataPacket) :
    afterHead native first headId head = WorkerEncryption.afterHead first headId head := rfl

theorem tail_native (item : Option (List SkbId)) : tail native item = WorkerEncryption.tail item := rfl

def focused (encode : WorkerEncryption.Receipt → E) (decode : E → Option WorkerEncryption.Receipt) : Ops E where
  step := fun action => focusPrefix encode decode (native.step action)
  head := fun id => focusPrefix encode decode (native.head id)
  packet := fun headId head id => focusPrefix encode decode (native.packet headId head id)
  publish := fun item state => focusPrefix encode decode (native.publish item state)

def observed (encode : WorkerEncryption.Receipt → E) (decode : E → Option WorkerEncryption.Receipt)
    (disposal : Event → E) (disposalDecode : E → Option Event) : Ops E :=
  {focused encode decode with
    publish := fun item state =>
      liftWGObserver (Publication.observed disposal disposalDecode item state)}

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.EncryptionSource
