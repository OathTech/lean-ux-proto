import Leanux.Proofs.WG.RetirementSecurity.OccurrenceJournalDeferred
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation

/-! The original fixture traffic paths carry physical poll certificates through
incoming datagrams, stack replies and deferred encryption in the shared journal. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
set_option maxHeartbeats 600000
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits OccurrenceStack TransmitSecurity

theorem ingress (msg : List UInt8) (src : SkbSource) : ProductSafe (Driver.receiveEntryObserved msg src) :=
  product_native _
    (RxPollOccurrences.join (ReceiveIngressCall.erases (.udp msg src)) (ReceiveIngressCall.allocation (.udp msg src))
      (ReceiveOccurrences.receive msg src))

theorem inline_poll : ProductSafe (Driver.inlinePollObserved Journal.hooks) := by
  apply join_history
  · exact (show Driver.inlinePollObserved nonpollHooks = Driver.inlinePollObserved Journal.hooks from rfl) ▸
      Driver.inline_history hooks_safe.actors
  · intro w h result v before run
    have projected := Driver.inline_projects Journal.hooks_projects
    rw [Driver.nonce_inlinePollObserved_eq] at projected
    exact (hoare_iff_run _ _ _).mp (OccurrenceNapi.inline [] []) w result v before
      (DriverOwnership.product_native projected Nonce.inlinePollObserved_erases w v h run)

theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    StateSafe (Driver.transmitObserved Journal.hooks family addr packets mtu) := by
  apply checked_state_history
  · exact (show Driver.transmitObserved nonpollHooks family addr packets mtu =
        Driver.transmitObserved Journal.hooks family addr packets mtu from rfl) ▸
      Driver.transmit_history hooks_safe.actors family addr packets mtu
  · intro w a h result v b before run
    have projected := Driver.transmit_projects Journal.hooks_projects family addr packets mtu
    rw [Driver.nonce_transmitObserved_eq] at projected
    have native := DriverOwnership.state_native projected (Nonce.transmitObserved_erases family addr packets mtu)
      w v a b h run
    exact ⟨before.1.transmit family addr packets mtu a b native,
      TransmitOccurrences.transmit ⟨before.1.bounded,before.2⟩ family addr packets mtu a b native⟩

theorem multicast (family addr : Nat) :
    ProductSafe (Driver.multicastObserved family addr) := by
  apply product_store
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
    ProductSafe (Driver.drainObserved what flags) :=
  product_store _ (Nonce.Frames.drained what flags)

theorem product_wg_store (h : List Journal.Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : (Inv []) h w) : (Inv []) h v :=
  ⟨ready_store same hi.1,hi.2⟩

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductSafe (Driver.injectObserved Journal.hooks family port msg tos ll dest) :=
  TrafficSource.inject_preserves (fun _ _ hi => hi.2) product_stable _ _ _ ingress crypt drain
    family port msg tos ll dest

theorem after_batch : ProductSafe (Driver.afterBatchObserved Journal.hooks) :=
  TrafficSource.afterBatch_preserves (fun _ _ hi => hi.2) product_stable _ _ _ _ _ crypt send_workers
    send_one schedule drain

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    ProductSafe (Driver.floodObserved Journal.hooks count port family messages) :=
  TrafficSource.flood_preserves (fun _ _ hi => hi.2) product_stable _ _ _ _ ingress inline_poll
    after_batch drain count port family messages

theorem batch_item (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductSafe (Driver.batchItemObserved Journal.hooks d cqes item) :=
  batchItemWith_preserves (fun _ _ hi => hi.2) product_wg_store _ _ _ _ ingress inline_poll multicast
    (fun family addr packets mtu => state_product (transmit family addr packets mtu)) d cqes item

theorem batch (items : List Env.BatchItem) : ProductSafe (Driver.batchObserved Journal.hooks items) :=
  TrafficSource.batch_preserves (fun _ _ hi => hi.2) product_stable _ _ batch_item after_batch items

theorem syscall_xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProductSafe (Driver.syscallXmitObserved Journal.hooks family addr payload opts) :=
  syscallXmitWith_preserves (fun _ _ hi => hi.2) product_wg_store _ _ multicast
    (fun family addr packets mtu => state_product (transmit family addr packets mtu)) family addr payload opts

end Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
