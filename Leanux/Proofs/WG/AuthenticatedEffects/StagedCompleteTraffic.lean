import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTrafficFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDeferred
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation

/-! The original fixture traffic wrappers carry paired accounting through
interleaved callbacks. Exact receive and scheduler contracts remain visible
until their concrete leaf joins; fixture transmission itself is discharged. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.Traffic
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Driver CompleteProduct

variable (scheduled : ∀ stack, Checked (scheduleObserved hooks stack))
variable (sentWork : Checked (sendWorkerObserved hooks))
variable (received : ∀ msg src, Checked (receiveEntryObserved hooks msg src))

include received scheduled in
theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Checked (injectObserved hooks family port msg tos ll dest) :=
  TrafficSource.inject_preserves carrier_safe stable _ _ _ received (Deferred.crypt scheduled)
    drain family port msg tos ll dest

include scheduled sentWork in
theorem afterBatch : Checked (afterBatchObserved hooks) :=
  DeliverySource.afterBatch_preserves carrier_safe stable _ _ _ _ _ _ (Deferred.crypt scheduled)
    (Deferred.sendWorkers scheduled sentWork) sentWork scheduled drain delivery

include received scheduled sentWork in
theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    Checked (floodObserved hooks count port family messages) :=
  TrafficSource.flood_preserves carrier_safe stable _ _ _ _ received inline_poll
    (afterBatch scheduled sentWork) drain count port family messages

include received in
theorem batchItem (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    Checked (batchItemObserved hooks d cqes item) :=
  batchItemWith_preserves carrier_safe store_transport _ _ _ _ received inline_poll multicast
    (fun family addr packets mtu => state (fixture _ _ (transmit family addr packets mtu))) d cqes item

include received scheduled sentWork in
theorem batch (items : List Env.BatchItem) : Checked (batchObserved hooks items) :=
  TrafficSource.batch_preserves carrier_safe stable _ _ (batchItem received)
    (afterBatch scheduled sentWork) items

theorem syscallXmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Checked (syscallXmitObserved hooks family addr payload opts) :=
  syscallXmitWith_preserves carrier_safe store_transport _ _ multicast
    (fun family addr packets mtu => state (fixture _ _ (transmit family addr packets mtu)))
    family addr payload opts

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.Traffic
