import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionEnvironment
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionDeferred
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionTrafficFrames

/-! Fixture ingress and traffic compose the actual poll, scheduler, transmit
and delivery observers. Every pre-clear buffer retains its ordered certificate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries.Carrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity.Driver
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option pp.structureInstances false

theorem ingress (msg : List UInt8) (src : SkbSource) : ProductSafe (receiveEntryObserved msg src) :=
  wg _ (EmissionFrames.receive msg src)

theorem multicast (family addr : Nat) : ProductSafe (multicastObserved family addr) :=
  native _ (EmissionFrames.multicast family addr)

theorem drain (what : String) (flags : List Bool) : ProductSafe (drainObserved what flags) :=
  native _ (EmissionFrames.drained what flags)

macro "emission_traffic_step" : tactic => `(tactic| first
  | contradiction
  | (emission_carrier_native_head Env.senderSource; exact native _ (EmissionFrames.sender _ _ _ _))
  | (emission_carrier_native_head Env.xmitPackets; exact native _ (EmissionFrames.xmit_packets _ _ _ _))
  | (emission_carrier_native_head Env.fixtureSend; unfold Env.fixtureSend; exact ambient _)
  | (emission_carrier_native_head requireNotPending; exact wg _ (by sent_frame [requireNotPending] using []))
  | (emission_carrier_head runWorkerPrefix; apply run_worker)
  | emission_outer_step)

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductSafe (injectObserved hooks family port msg tos ll dest) := by
  unfold injectObserved TrafficSource.injectWith
  repeat' first
    | (emission_carrier_head receiveEntryObserved; exact ingress _ _)
    | (emission_carrier_head cryptObserved; exact crypt)
    | (emission_carrier_head drainObserved; exact drain _ _)
    | emission_traffic_step

theorem after_batch : ProductSafe (afterBatchObserved hooks) := by
  unfold afterBatchObserved DeliverySource.afterBatchWith
  repeat' first
    | (emission_carrier_head Hooks.deliver; exact deliver)
    | (emission_carrier_head cryptObserved; exact crypt)
    | (emission_carrier_head sendWorkersObserved; exact send_workers)
    | (emission_carrier_head sendWorkerObserved; exact send_worker)
    | (emission_carrier_head scheduleObserved; exact schedule _)
    | (emission_carrier_head drainObserved; exact drain _ _)
    | emission_traffic_step

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    ProductSafe (floodObserved hooks count port family messages) := by
  unfold floodObserved TrafficSource.floodWith
  repeat' first
    | (emission_carrier_head receiveEntryObserved; exact ingress _ _)
    | (emission_carrier_head inlinePollObserved; exact inline_poll)
    | (emission_carrier_head afterBatchObserved; exact after_batch)
    | (emission_carrier_head drainObserved; exact drain _ _)
    | emission_traffic_step

theorem batch_item (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductSafe (batchItemObserved hooks d cqes item) := by
  cases item
  all_goals unfold batchItemObserved batchItemWith
  all_goals repeat' first
    | (emission_carrier_head receiveEntryObserved; exact ingress _ _)
    | (emission_carrier_head inlinePollObserved; exact inline_poll)
    | (emission_carrier_head multicastObserved; exact multicast _ _)
    | (emission_carrier_head FixtureEffects.runWith; exact product_state (fixture _ _ (device_transmit _ _ _ _)))
    | emission_traffic_step

theorem batch (items : List Env.BatchItem) : ProductSafe (batchObserved hooks items) := by
  unfold batchObserved TrafficSource.batchWith
  repeat' first
    | (emission_carrier_head batchItemObserved; exact batch_item _ _ _)
    | (emission_carrier_head afterBatchObserved; exact after_batch)
    | emission_traffic_step

theorem syscall_xmit (family addr : Nat) (bytes : List UInt8) (opts : Env.XmitOpts) :
    ProductSafe (syscallXmitObserved hooks family addr bytes opts) := by
  unfold syscallXmitObserved syscallXmitWith
  apply socket_call
  repeat' first
    | (emission_carrier_head multicastObserved; exact multicast _ _)
    | (emission_carrier_head FixtureEffects.runWith; exact product_state (fixture _ _ (device_transmit _ _ _ _)))
    | emission_traffic_step

theorem observe : ProductSafe (observeObserved hooks) := by
  unfold observeObserved DeliverySource.observeWith
  exact product_bind idle_timers (fun _ => product_bind (native _ EmissionFrames.observe_front)
    (fun _ => product_bind deliver (fun _ => native _ EmissionFrames.observe_finish)))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries.Carrier
