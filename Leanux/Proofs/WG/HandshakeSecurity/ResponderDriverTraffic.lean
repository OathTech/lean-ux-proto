import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverTrafficFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

theorem receive_entry (msg : List UInt8) (src : SkbSource) :
    ProductPreserves (Driver.receiveEntryObserved msg src) :=
  product_native _ (carrier_rx_entry msg src)

theorem multicast (family addr : Nat) :
    ProductPreserves (Driver.multicastObserved family addr) :=
  product_lift _ (carrier_multicast family addr)

theorem drain (what : String) (flags : List Bool) :
    ProductPreserves (Driver.drainObserved what flags) :=
  product_store _ (Nonce.Frames.drained what flags)

theorem inject (H1 : H1ResponderCurrentEdges) (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductPreserves (Driver.injectObserved hooks family port msg tos ll dest) :=
  TrafficSource.inject_preserves (fun _ _ hi => hi.2) product_stable _ _ _
    receive_entry (crypt H1) drain family port msg tos ll dest

theorem after_batch (H1 : H1ResponderCurrentEdges) :
    ProductPreserves (Driver.afterBatchObserved hooks) :=
  TrafficSource.afterBatch_preserves (fun _ _ hi => hi.2) product_stable _ _ _ _ _
    (crypt H1) (send_workers H1) (by rw [Driver.sendWorker_lift hooks rfl]; exact send_one) (schedule H1) drain

theorem flood (H1 : H1ResponderCurrentEdges) (count port family : Nat)
    (messages : List (List UInt8)) :
    ProductPreserves (Driver.floodObserved hooks count port family messages) :=
  TrafficSource.flood_preserves (fun _ _ hi => hi.2) product_stable _ _ _ _
    receive_entry (inline_poll H1) (after_batch H1) drain count port family messages

theorem batch_item (H1 : H1ResponderCurrentEdges) (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductPreserves (Driver.batchItemObserved hooks d cqes item) := by
  unfold Driver.batchItemObserved
  simp only [show Driver.fixtureOps hooks = AuthenticatedEffects.FixtureEffects.neutral from rfl,
    AuthenticatedEffects.FixtureEffects.run_neutral]
  exact batchItemWith_preserves (fun _ _ hi => hi.2) product_wg_stable _ _ _ _
    receive_entry (inline_poll H1) multicast
    (fun family addr packets mtu => product_safe (transmit family addr packets mtu)) d cqes item

theorem batch (H1 : H1ResponderCurrentEdges) (items : List Env.BatchItem) :
    ProductPreserves (Driver.batchObserved hooks items) :=
  TrafficSource.batch_preserves (fun _ _ hi => hi.2) product_stable _ _
    (batch_item H1) (after_batch H1) items

theorem syscall_xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProductPreserves (Driver.syscallXmitObserved hooks family addr payload opts) := by
  unfold Driver.syscallXmitObserved
  simp only [show Driver.fixtureOps hooks = AuthenticatedEffects.FixtureEffects.neutral from rfl,
    AuthenticatedEffects.FixtureEffects.run_neutral]
  exact syscallXmitWith_preserves (fun _ _ hi => hi.2) product_wg_stable _ _ multicast
    (fun family addr packets mtu => product_safe (transmit family addr packets mtu)) family addr payload opts

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
