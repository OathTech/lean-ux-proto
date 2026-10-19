import Leanux.Proofs.WG.HandshakeSecurity.ExchangeTrafficFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

theorem receive_entry (traffic : H1TrafficTagFrames) (msg : List UInt8) (src : SkbSource) :
    ProductPreserves (Driver.receiveEntryObserved ExchangeDriver.hooks msg src) := by
  rw [Driver.receiveEntry_lift ExchangeDriver.hooks rfl,liftWGObserver_lift]
  exact product_native _ (fun h => frame h _ (traffic.receive msg src))

theorem multicast (family addr : Nat) :
    ProductPreserves (Driver.multicastObserved family addr) :=
  product_lift _ (multicast_frame family addr)

theorem drain (what : String) (flags : List Bool) :
    ProductPreserves (Driver.drainObserved what flags) :=
  product_store _ (Nonce.Frames.drained what flags)

theorem transmit_checked (traffic : H1TrafficTagFrames) (family addr : Nat)
    (packets : List Packet) (mtu : Nat) :
    Preserves (Driver.transmitObserved ExchangeDriver.hooks family addr packets mtu) := by
  rw [ExchangeDriver.transmit_lift]
  exact lift _ (fun h => frame h _ (traffic.transmit family addr packets mtu))

theorem inject (facts : H1DriverSourceFacts) (traffic : H1TrafficTagFrames) (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductPreserves (Driver.injectObserved ExchangeDriver.hooks family port msg tos ll dest) :=
  TrafficSource.inject_preserves (fun _ _ hi => hi.safe) product_stable _ _ _
    (receive_entry traffic) (crypt facts) drain family port msg tos ll dest

theorem after_batch (facts : H1DriverSourceFacts) :
    ProductPreserves (Driver.afterBatchObserved ExchangeDriver.hooks) :=
  TrafficSource.afterBatch_preserves (fun _ _ hi => hi.safe) product_stable _ _ _ _ _
    (crypt facts) (send_workers facts) (send_one_checked facts.edges facts.handshake) (schedule_checked facts.edges facts.handshake facts.data facts.workers) drain

theorem flood (facts : H1DriverSourceFacts) (traffic : H1TrafficTagFrames) (count port family : Nat)
    (messages : List (List UInt8)) :
    ProductPreserves (Driver.floodObserved ExchangeDriver.hooks count port family messages) :=
  TrafficSource.flood_preserves (fun _ _ hi => hi.safe) product_stable _ _ _ _
    (receive_entry traffic) (inline_checked facts.workers) (after_batch facts) drain count port family messages

theorem batch_item (facts : H1DriverSourceFacts) (traffic : H1TrafficTagFrames) (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductPreserves (Driver.batchItemObserved ExchangeDriver.hooks d cqes item) := by
  unfold Driver.batchItemObserved
  simp only [show Driver.fixtureOps ExchangeDriver.hooks = AuthenticatedEffects.FixtureEffects.neutral from rfl,
    AuthenticatedEffects.FixtureEffects.run_neutral]
  exact batchItemWith_preserves (fun _ _ hi => hi.safe) product_wg_stable _ _ _ _
    (receive_entry traffic) (inline_checked facts.workers) multicast
    (fun family addr packets mtu => product_state (transmit_checked traffic family addr packets mtu)) d cqes item

theorem batch (facts : H1DriverSourceFacts) (traffic : H1TrafficTagFrames) (items : List Env.BatchItem) :
    ProductPreserves (Driver.batchObserved ExchangeDriver.hooks items) :=
  TrafficSource.batch_preserves (fun _ _ hi => hi.safe) product_stable _ _
    (batch_item facts traffic) (after_batch facts) items

theorem syscall_xmit (traffic : H1TrafficTagFrames) (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProductPreserves (Driver.syscallXmitObserved ExchangeDriver.hooks family addr payload opts) := by
  unfold Driver.syscallXmitObserved
  simp only [show Driver.fixtureOps ExchangeDriver.hooks = AuthenticatedEffects.FixtureEffects.neutral from rfl,
    AuthenticatedEffects.FixtureEffects.run_neutral]
  exact syscallXmitWith_preserves (fun _ _ hi => hi.safe) product_wg_stable _ _ multicast
    (fun family addr packets mtu => product_state (transmit_checked traffic family addr packets mtu)) family addr payload opts

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
