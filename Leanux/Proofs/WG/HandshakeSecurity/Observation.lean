import Leanux.Proofs.WG.HandshakeSecurity.Source

/-! Timestamp receipts are emitted immediately after the actual write, before
the subsequent consumption-clock read. They survive a later Stop. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged

structure TimestampReceipt where
  peer : PeerId
  compared : List UInt8
  received : List UInt8
  execution : WGRunWitness Unit

def TimestampReceipt.Valid (r : TimestampReceipt) : Prop :=
  r.execution.Valid (writeTimestamp r.peer r.received)

def TimestampReceipt.Newer (r : TimestampReceipt) : Prop :=
  memcmp r.received r.compared = .gt

def timestampObserved (pid : PeerId) (old t : List UInt8) : WGPrefix TimestampReceipt Unit := do
  if ← liftWGPrefix (branch .consumeNewerTimestamp (memcmp t old == .gt)) then
    receiptWGObserved (liftWGPrefix (writeTimestamp pid t)) (fun r => ⟨pid, old, t, r⟩)

def consumeObserved (msg : List UInt8) : WGPrefix TimestampReceipt (Option PeerId) :=
  consumeWith liftWGPrefix timestampObserved msg

theorem timestamp_erases (pid : PeerId) (old t : List UInt8) :
    ErasesStatePrefix (timestampObserved pid old t) (timestampStep pid old t) := by
  unfold timestampObserved timestampStep
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro b
  split
  · exact receiptWGObserved_erases (erasesStatePrefix_lift _) _
  · exact erasesStatePrefix_pure _

theorem consume_erases (msg : List UInt8) :
    ErasesStatePrefix (consumeObserved msg) (consumeInitiation msg) := by
  have lifted {α : Type} (a : WG.M α) : ErasesStatePrefix (liftWGPrefix a : WGPrefix TimestampReceipt α) a :=
    erasesStatePrefix_lift a
  rw [← consume_factor]
  unfold consumeObserved consumeWith checkedWith successWith
  repeat' first
    | with_reducible exact timestamp_erases _ _ _
    | with_reducible exact lifted _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (session_origin_intro_forall; try dsimp only)
    | split

end Leanux.Proofs.WG.HandshakeSecurity
