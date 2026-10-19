import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceIngress

namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
variable {E : Type} [EntryFormat E]
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

theorem receive_entry (msg : List UInt8) (src : SkbSource) :
    ProductPreserves (E := E) (Driver.receiveEntryObserved EntrySource.hooks msg src) := by
  rw [Driver.receiveEntry_lift EntrySource.hooks rfl,liftWGObserver_lift]
  exact product_native _ (rx_entry msg src)

theorem multicast (family addr : Nat) :
    ProductPreserves (E := E) (Driver.multicastObserved family addr) :=
  product_lift _ (multicast_native family addr)

theorem drain (what : String) (flags : List Bool) :
    ProductPreserves (E := E) (Driver.drainObserved what flags) :=
  product_store _ (Nonce.Frames.drained what flags)

theorem inject (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    ProductPreserves (E := E) (Driver.injectObserved EntrySource.hooks (E := E) family port msg tos ll dest) :=
  TrafficSource.inject_preserves (fun _ _ hi => hi.1) product_stable _ _ _
    receive_entry (crypt) drain family port msg tos ll dest

theorem after_batch :
    ProductPreserves (E := E) (Driver.afterBatchObserved EntrySource.hooks (E := E)) :=
  TrafficSource.afterBatch_preserves (fun _ _ hi => hi.1) product_stable _ _ _ _ _
    (crypt) (send_workers) send_one (schedule) drain

theorem flood (count port family : Nat)
    (messages : List (List UInt8)) :
    ProductPreserves (E := E) (Driver.floodObserved EntrySource.hooks (E := E) count port family messages) :=
  TrafficSource.flood_preserves (fun _ _ hi => hi.1) product_stable _ _ _ _
    receive_entry (inline_poll) (after_batch) drain count port family messages

theorem batch_item (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProductPreserves (E := E) (Driver.batchItemObserved EntrySource.hooks (E := E) d cqes item) := by
  unfold Driver.batchItemObserved
  simp only [show Driver.fixtureOps EntrySource.hooks (E := E) = AuthenticatedEffects.FixtureEffects.neutral from rfl,
    AuthenticatedEffects.FixtureEffects.run_neutral]
  exact batchItemWith_preserves (fun _ _ hi => hi.1) product_wg_stable _ _ _ _
    receive_entry (inline_poll) multicast
    (fun family addr packets mtu => product_safe (transmit family addr packets mtu)) d cqes item

theorem batch (items : List Env.BatchItem) :
    ProductPreserves (E := E) (Driver.batchObserved EntrySource.hooks (E := E) items) :=
  TrafficSource.batch_preserves (fun _ _ hi => hi.1) product_stable _ _
    (batch_item) (after_batch) items

theorem syscall_xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    ProductPreserves (E := E) (Driver.syscallXmitObserved EntrySource.hooks (E := E) family addr payload opts) := by
  unfold Driver.syscallXmitObserved
  simp only [show Driver.fixtureOps EntrySource.hooks (E := E) = AuthenticatedEffects.FixtureEffects.neutral from rfl,
    AuthenticatedEffects.FixtureEffects.run_neutral]
  exact syscallXmitWith_preserves (fun _ _ hi => hi.1) product_wg_stable _ _ multicast
    (fun family addr packets mtu => product_safe (transmit family addr packets mtu)) family addr payload opts

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
