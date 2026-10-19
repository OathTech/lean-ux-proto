import Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntryDeferred
import Leanux.Proofs.WG.AuthenticatedEffects.DeliveryPreservation

/-! Fixture ingress and transmit batches carry coherence through their actual
interleaved poll and deferred callbacks. Fixture scopes are neutral in this projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Keypairs TransmitSecurity.Driver

abbrev ProductInv (h : List Event) (w : World) := Inv w.wg ∧ Safe h

theorem product_wg_store (h : List Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : ProductInv h w) : ProductInv h v := by
  have snap := congrArg Keypairs.snapshotOfWGStoreView same
  change snapshot v.wg = snapshot w.wg at snap
  exact ⟨by simpa only [Inv,snap] using hi.1,hi.2⟩

private theorem safe (h : List Event) (w : World) (hi : ProductInv h w) : Safe h := hi.2

theorem ingress (msg : List UInt8) (src : SkbSource) : ProductSafe (receiveEntryObserved hooks msg src) := by
  rw [receiveEntry_lift hooks rfl]
  simpa only [liftWGObserver_lift] using
    product_state (state_native _ (WGMore.wgReceive_ordinary msg src))

theorem multicast (family addr : Nat) : ProductSafe (multicastObserved family addr) :=
  product_same _ (EnvFrames.xmitMulticastLoop_sameSnapshot family addr)

theorem drain (what : String) (flags : List Bool) : ProductSafe (drainObserved what flags) :=
  product_storeLift _ (TransmitSecurity.Nonce.Frames.drained what flags)

theorem transmit_erases (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ErasesStatePrefix (transmitObserved hooks family addr packets mtu) (wgXmit family addr packets mtu) := by
  apply state_native_result (transmit_projects native_projects family addr packets mtu)
    (transmit_projects HandshakeSecurity.NativeDriver.nonce_projection family addr packets mtu)
  rw [nonce_transmitObserved_eq]
  exact TransmitSecurity.Nonce.transmitObserved_erases family addr packets mtu

theorem transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (transmitObserved hooks family addr packets mtu) := by
  apply state_observed _ _ (transmit_erases family addr packets mtu) _
    (WGDevice.wgXmit_ordinary family addr packets mtu)
  change StateHistorySafe Safe (transmitObserved quietHooks family addr packets mtu)
  exact transmit_history (quiet_history Safe).core family addr packets mtu

theorem fixture (trigger : FixtureEffects.Trigger) (body : WGPrefix Event α) (hb : StateSafe body) :
    StateSafe (FixtureEffects.runWith (fixtureOps hooks) trigger body) := by
  change StateSafe (FixtureEffects.runWith FixtureEffects.neutral trigger body)
  rw [FixtureEffects.run_neutral]
  exact hb

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductSafe (injectObserved hooks family port msg tos ll dest) :=
  TrafficSource.inject_preserves safe product_store _ _ _ ingress crypt drain family port msg tos ll dest

theorem after_batch : ProductSafe (afterBatchObserved hooks) :=
  DeliverySource.afterBatch_preserves safe product_store _ _ _ _ _ _ crypt send_workers
    send_worker schedule drain deliver

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    ProductSafe (floodObserved hooks count port family messages) :=
  TrafficSource.flood_preserves safe product_store _ _ _ _ ingress inline_poll after_batch drain count port family messages

theorem batch_item (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductSafe (batchItemObserved hooks d cqes item) :=
  batchItemWith_preserves safe product_wg_store _ _ _ _ ingress inline_poll multicast
    (fun family addr packets mtu => product_state (fixture _ _ (transmit family addr packets mtu))) d cqes item

theorem batch (items : List Env.BatchItem) : ProductSafe (batchObserved hooks items) :=
  TrafficSource.batch_preserves safe product_store _ _ batch_item after_batch items

theorem syscall_xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProductSafe (syscallXmitObserved hooks family addr payload opts) :=
  syscallXmitWith_preserves safe product_wg_store _ _ multicast
    (fun family addr packets mtu => product_state (fixture _ _ (transmit family addr packets mtu))) family addr payload opts

end Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
