import Leanux.Proofs.WG.Campaign2.View
import Leanux.Proofs.WG.Index.AllocationModel

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Campaign2

/-- The entry snapshot and result of one actual original call. -/
structure SessionAllocationCall where
  pid : PeerId
  entry : Snapshot
  result : Bool

/-- Successful IDs come from the observed entry device, not a generated counter
trace. The source contract establishes that every observation has a device. -/
def sessionSuccessfulIds (calls : List SessionAllocationCall) : List KeypairId :=
  calls.filterMap fun call =>
    if call.result then call.entry.wg.device.map Device.nextKeypairId else none

structure SessionAllocationSequenceFacts (initial : Device) (pids : List PeerId)
    (calls : List SessionAllocationCall) (final : Snapshot) : Prop where
  peers : calls.map SessionAllocationCall.pid = pids
  length : (calls.map SessionAllocationCall.result).length = pids.length
  entries : ∀ call ∈ calls, ∃ d, call.entry.wg.device = some d ∧
    KeypairStoreBounded d ∧ d.keypairs[d.nextKeypairId]? = none
  ids : sessionSuccessfulIds calls =
    List.range' initial.nextKeypairId ((calls.map SessionAllocationCall.result).count true)
  distinct : (sessionSuccessfulIds calls).Nodup
  finalBound : ∃ d, final.wg.device = some d ∧ KeypairStoreBounded d ∧
    d.nextKeypairId = initial.nextKeypairId +
      (calls.map SessionAllocationCall.result).count true

end Leanux.Proofs.WG.Index
