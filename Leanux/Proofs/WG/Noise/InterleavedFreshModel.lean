import Leanux.Proofs.WG.Noise.FreshHistoryModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- One existing native operation with its actual actor. Consumer messages still
select their returned peer internally, exactly as the existing operation does. -/
abbrev InterleavedFreshOperation := PeerId × FreshOperation

structure InterleavedFreshReceipt where
  actor : PeerId
  call : FreshReceipt

/-- Successful confirmations of the tracked peer only. Numeric identities
confirmed by another peer are not silently counted as the tracked peer's event. -/
def InterleavedFreshReceipt.confirmed (tracked : PeerId) (receipt : InterleavedFreshReceipt) :
    Option KeypairId := if receipt.actor = tracked then receipt.call.confirmed else none

def interleavedConfirmedIds (tracked : PeerId) : List InterleavedFreshReceipt → List KeypairId
  | [] => []
  | receipt :: rest => interleavedConfirmedIds tracked rest ++ (receipt.confirmed tracked).toList

/-- The tracked operation's original effect, or another peer's successful
allocation, which advances the shared cursor without changing the tracked slot. -/
inductive InterleavedFreshStep : (Option Nat × Option (Option KeypairId)) → Option KeypairId →
    (Option Nat × Option (Option KeypairId)) → Prop where
  | localStep {before after confirmed} (step : FreshViewStep before confirmed after) :
      InterleavedFreshStep before confirmed after
  | advance (cursor : Nat) (next : Option (Option KeypairId)) :
      InterleavedFreshStep (some cursor,next) none (some (cursor+1),next)

/-- Linked projected boundaries and actor/operation order. The source theorem
derives this relation from actual native calls. The finite operation language
excludes peer recreation and device reset. -/
inductive InterleavedFreshChain (tracked : PeerId) : Campaign2.Snapshot →
    List InterleavedFreshOperation → List InterleavedFreshReceipt → Campaign2.Snapshot → Prop where
  | nil (entry) : InterleavedFreshChain tracked entry [] [] entry
  | cons (receipt : InterleavedFreshReceipt) (operations : List InterleavedFreshOperation)
      (receipts : List InterleavedFreshReceipt) (final : Campaign2.Snapshot)
      (step : InterleavedFreshStep (freshInstallView tracked receipt.call.before.wg.device)
        (receipt.confirmed tracked) (freshInstallView tracked receipt.call.after.wg.device))
      (tail : InterleavedFreshChain tracked receipt.call.after operations receipts final) :
      InterleavedFreshChain tracked receipt.call.before ((receipt.actor,receipt.call.operation)::operations)
        (receipt::receipts) final

end Leanux.Proofs.WG.Noise
