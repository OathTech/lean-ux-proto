import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixTrafficFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDeferred
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation

/-! The original traffic wrappers retain all earlier logical prefixes through
interleaved callbacks. Receive, scheduler, inline poll and transmit prefix
contracts remain explicit until their concrete source joins. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product.Traffic
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Driver CompletePrefix.Product

variable (scheduled : ∀ stack, Checked (scheduleObserved hooks stack))
variable (sentWork : Checked (sendWorkerObserved hooks))
variable (received : ∀ msg src, Checked (receiveEntryObserved hooks msg src))
variable (inlineProof : Checked (Driver.inlinePollObserved hooks))
variable (transmitProof : ∀ family addr packets mtu, StateChecked (Driver.transmitObserved hooks family addr packets mtu))

include received scheduled in
theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Checked (injectObserved hooks family port msg tos ll dest) :=
  TrafficSource.inject_preserves carrier_safe stable _ _ _ received (Deferred.crypt scheduled)
    drain family port msg tos ll dest

include scheduled sentWork in
theorem afterBatch : Checked (afterBatchObserved hooks) :=
  DeliverySource.afterBatch_preserves carrier_safe stable _ _ _ _ _ _ (Deferred.crypt scheduled)
    (Deferred.sendWorkers scheduled sentWork) sentWork scheduled drain delivery

include received scheduled sentWork inlineProof in
theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    Checked (floodObserved hooks count port family messages) :=
  TrafficSource.flood_preserves carrier_safe stable _ _ _ _ received inlineProof
    (afterBatch scheduled sentWork) drain count port family messages

include received inlineProof transmitProof in
theorem batchItem (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    Checked (batchItemObserved hooks d cqes item) :=
  batchItemWith_preserves carrier_safe store_transport _ _ _ _ received inlineProof multicast
    (fun family addr packets mtu => state (fixture _ _ (transmitProof family addr packets mtu))) d cqes item

include received scheduled sentWork inlineProof transmitProof in
theorem batch (items : List Env.BatchItem) : Checked (batchObserved hooks items) :=
  TrafficSource.batch_preserves carrier_safe stable _ _ (batchItem received inlineProof transmitProof)
    (afterBatch scheduled sentWork) items

include transmitProof in
theorem syscallXmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Checked (syscallXmitObserved hooks family addr payload opts) :=
  syscallXmitWith_preserves carrier_safe store_transport _ _ multicast
    (fun family addr packets mtu => state (fixture _ _ (transmitProof family addr packets mtu)))
    family addr payload opts

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product.Traffic
