import Leanux.Proofs.WG.Campaign2.View
import Leanux.WG.Handshake

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- Explicit calls in a finite native history. This is not an environment
scheduler or an exhaustive model of every driver entry. -/
inductive TagOperation where
  | createInitiation (pid : PeerId)
  | createResponse (pid : PeerId)
  | consumeInitiation (message : List UInt8)
  | consumeResponse (message : List UInt8)
  | beginSession (pid : PeerId)
  | handshakeClear (pid : PeerId)
  | expireCurrentPeerKeypairs (pid : PeerId)

/-- The original result, including the entire created message. -/
inductive TagReturn where
  | created (message : Option (List UInt8))
  | consumed (peer : Option PeerId)
  | begun (ok : Bool)
  | cleared

/-- Actual native snapshots before and after one normally completed call. -/
structure TagReceipt where
  operation : TagOperation
  before : Campaign2.Snapshot
  result : TagReturn
  after : Campaign2.Snapshot

/-- All optional peer tags are accounted for. Initiation creation and
consumption admit restarts from arbitrary tags. Other guarded edges retain
their actual old-tag requirements; normal refusals preserve the whole map. -/
def TagReceiptEffect (r : TagReceipt) : Prop :=
  match r.operation, r.result with
  | .createInitiation pid, .created result =>
    ∀ target, r.after.tagAt target =
      if result.isSome then
        if pid = target then some HANDSHAKE_CREATED_INITIATION else r.before.tagAt target
      else r.before.tagAt target
  | .createResponse pid, .created result =>
    (∀ target, r.after.tagAt target =
      if result.isSome then
        if pid = target then some HANDSHAKE_CREATED_RESPONSE else r.before.tagAt target
      else r.before.tagAt target) ∧
    (result.isSome → r.before.tagAt pid = some HANDSHAKE_CONSUMED_INITIATION)
  | .consumeInitiation _, .consumed result =>
    ∀ pid, r.after.tagAt pid = if result = some pid then
      some HANDSHAKE_CONSUMED_INITIATION else r.before.tagAt pid
  | .consumeResponse _, .consumed result =>
    (∀ pid, r.after.tagAt pid = if result = some pid then
      some HANDSHAKE_CONSUMED_RESPONSE else r.before.tagAt pid) ∧
    (∀ pid, result = some pid → r.before.tagAt pid = some HANDSHAKE_CREATED_INITIATION)
  | .beginSession pid, .begun ok =>
    (∀ target, r.after.tagAt target =
      if ok then if pid = target then some HANDSHAKE_ZEROED else r.before.tagAt target
      else r.before.tagAt target) ∧
    (ok = true → r.before.tagAt pid = some HANDSHAKE_CREATED_RESPONSE ∨
      r.before.tagAt pid = some HANDSHAKE_CONSUMED_RESPONSE)
  | .handshakeClear pid, .cleared | .expireCurrentPeerKeypairs pid, .cleared =>
    ∀ target, r.after.tagAt target =
      if pid = target then some HANDSHAKE_ZEROED else r.before.tagAt target
  | _, _ => False

/-- The whole projected exit of each call is the next call's entry.
Receipt order and length are exactly those of the supplied operations. -/
inductive TagChain : Campaign2.Snapshot → List TagOperation →
    List TagReceipt → Campaign2.Snapshot → Prop where
  | nil (entry : Campaign2.Snapshot) : TagChain entry [] [] entry
  | cons (receipt : TagReceipt) (operations : List TagOperation)
      (receipts : List TagReceipt) (final : Campaign2.Snapshot)
      (edge : TagReceiptEffect receipt)
      (tail : TagChain receipt.after operations receipts final) :
      TagChain receipt.before (receipt.operation :: operations) (receipt :: receipts) final

end Leanux.Proofs.WG.Noise
