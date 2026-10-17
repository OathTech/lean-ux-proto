import Leanux.Proofs.WG.Noise.FreshInstallModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- This finite language uses actual responder setup, session allocation and
confirmation calls for one tracked peer. It excludes direct helper installation,
peer recreation and device reset; it is not the driver scheduler. -/
inductive FreshOperation where
  | consume (message : List UInt8)
  | respond
  | beginSession
  | confirm (id : KeypairId)

/-- Original returns, including the entire created response. -/
inductive FreshReturn where
  | consumed (peer : Option PeerId)
  | created (message : Option (List UInt8))
  | begun (ok : Bool)
  | confirmed (ok : Bool)

structure FreshReceipt where
  operation : FreshOperation
  before : Campaign2.Snapshot
  result : FreshReturn
  after : Campaign2.Snapshot

def FreshReceipt.confirmed : FreshReceipt → Option KeypairId
  | ⟨.confirm id, _, .confirmed true, _⟩ => some id
  | _ => none

/-- Confirmation IDs in reverse receipt order. Distinctness is independent of
this presentation order; the receipts themselves remain in execution order. -/
def freshConfirmedIds : List FreshReceipt → List KeypairId
  | [] => []
  | receipt :: rest => freshConfirmedIds rest ++ receipt.confirmed.toList

/-- The small cursor/next effect used only for confirmation history. Successful
allocation chooses the old cursor and advances it; it need not leave a resident
key because arbitrary rotation aliases and their failures remain modeled. -/
inductive FreshViewStep : (Option Nat × Option (Option KeypairId)) → Option KeypairId →
    (Option Nat × Option (Option KeypairId)) → Prop where
  | same (view) : FreshViewStep view none view
  | allocate (cursor : Nat) (beforeNext : Option (Option KeypairId))
      (next : Option KeypairId) (role : next = none ∨ next = some cursor) :
      FreshViewStep (some cursor,beforeNext) none (some (cursor+1),some next)
  | confirm (cursor id : Nat) :
      FreshViewStep (some cursor,some (some id)) (some id) (some cursor,some none)

/-- Actual complete projected boundaries are linked, with exact operation order.
No intermediate execution or ready input is supplied as a premise. -/
inductive FreshChain (pid : PeerId) : Campaign2.Snapshot → List FreshOperation →
    List FreshReceipt → Campaign2.Snapshot → Prop where
  | nil (entry) : FreshChain pid entry [] [] entry
  | cons (receipt : FreshReceipt) (operations : List FreshOperation)
      (receipts : List FreshReceipt) (final : Campaign2.Snapshot)
      (step : FreshViewStep (freshInstallView pid receipt.before.wg.device)
        receipt.confirmed (freshInstallView pid receipt.after.wg.device))
      (tail : FreshChain pid receipt.after operations receipts final) :
      FreshChain pid receipt.before (receipt.operation::operations) (receipt::receipts) final


/-- Internal history invariant: completed IDs are below the current cursor and
cannot still occupy next. This is a numeric-ID invariant, not key residency. -/
structure FreshSeen (view : Option Nat × Option (Option KeypairId)) (seen : List KeypairId) : Prop where
  distinct : seen.Nodup
  past : ∀ id ∈ seen, ∀ cursor, view.1 = some cursor → id < cursor
  away : ∀ id ∈ seen, view.2 ≠ some (some id)
  next : ∀ cursor id, view.1 = some cursor → view.2 = some (some id) → id < cursor


end Leanux.Proofs.WG.Noise
