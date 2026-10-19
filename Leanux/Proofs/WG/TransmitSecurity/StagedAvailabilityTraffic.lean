import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityDeferred
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityIngressFrames
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation
import Leanux.Proofs.WG.AuthenticatedEffects.DeliveryPreservation

/-! Actual fixture ingress, flood, batch and transmit callbacks transport staged
origins through their interleaved native worker and poll schedule. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Driver AuthenticatedEffects AuthenticatedEffects.CausalJournal
theorem ingress (msg : List UInt8) (src : SkbSource) :
    ProductSafe (receiveEntryObserved msg src) := by
  simpa only [receiveEntryObserved,liftWGObserver_lift] using product_state (state_lift _ (fun _ => Native.receive msg src))

theorem multicast (family addr : Nat) :
    ProductSafe (multicastObserved family addr) := by
  apply product_store_lift
  intro initial
  change Framing.Preserves (fun w : World => productStoreView w = initial) _
  have loop : Framing.Preserves (fun w : World => productStoreView w = initial)
      (monadLift (loopbackSend [] true) : Leanux.M Unit) :=
    liftWG_sameProductStore _ (loopbackSend_kernel [] true) initial
  have ambient {α : Type} (a : AmbientM α) :
      Framing.Preserves (fun w : World => productStoreView w = initial) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  routing_tx_source [Env.xmitMulticastLoop] using [loop,ambient]

theorem drain (what : String) (flags : List Bool) :
    ProductSafe (drainObserved what flags) :=
  product_store_lift _ (TransmitSecurity.Nonce.Frames.drained what flags)

private theorem safe (h : List Event) (w : World) (before : Carrier h w.wg) : Safe h := before.2

theorem fixture (trigger : FixtureEffects.Trigger) (body : WGPrefix Event α) (safe : StateSafe body) :
    StateSafe (FixtureEffects.runWith (fixtureOps hooks) trigger body) := by
  unfold FixtureEffects.runWith
  apply state_bind
  · intro w a h before
    have good := before.2.emit (quiet_event (event := .scope (.entered ⟨h.length,.fixture trigger⟩)) rfl)
    exact ⟨[.scope (.entered ⟨h.length,.fixture trigger⟩)],rfl,good,before.1.append (fun _ _ member => no_use (by simp only [List.mem_singleton] at member; subst_vars; rfl)),good⟩
  · intro token
    exact state_bind safe (fun value => state_bind (state_emit _ rfl) (fun _ => state_pure value))

theorem inject (family port : Nat)
    (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductSafe (injectObserved hooks family port msg tos ll dest) :=
  TrafficSource.inject_preserves safe product_stable _ _ _ ingress crypt drain family port msg tos ll dest

theorem afterBatch :
    ProductSafe (afterBatchObserved hooks) :=
  DeliverySource.afterBatch_preserves safe product_stable _ _ _ _ _ _ crypt sendWorkers
    send_worker schedule drain delivery

theorem flood (count port family : Nat)
    (messages : List (List UInt8)) :
    ProductSafe (floodObserved hooks count port family messages) :=
  TrafficSource.flood_preserves safe product_stable _ _ _ _ ingress inline_poll
    afterBatch drain count port family messages

theorem batchItem
    (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductSafe (batchItemObserved hooks d cqes item) :=
  batchItemWith_preserves safe product_wg_store _ _ _ _ ingress inline_poll multicast
    (fun family addr packets mtu => product_state (fixture _ _
      (transmit_observed family addr packets mtu))) d cqes item

theorem batch
    (items : List Env.BatchItem) : ProductSafe (batchObserved hooks items) :=
  TrafficSource.batch_preserves safe product_stable _ _ batchItem afterBatch items

theorem syscallXmit
    (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProductSafe (syscallXmitObserved hooks family addr payload opts) :=
  syscallXmitWith_preserves safe product_wg_store _ _ multicast
    (fun family addr packets mtu => product_state (fixture _ _
      (transmit_observed family addr packets mtu)))
    family addr payload opts

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
