import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteNativeCalls
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConfigurationClosed

/-! Whole source contracts retain paired packet accounting and independently
transport native allocation state along the same run. All internal staging,
keepalive, handshake-session and release callbacks are concrete. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

theorem staging (pid : PeerId) : StateChecked (Driver.stagingObserved hooks pid) :=
  pair (source_state (CompleteTransmit.staging pid)) (ConfigurationNative.staging_erases pid)
    (ConfigurationNative.staging pid)

theorem keepalive (pid : PeerId) : StateChecked (Driver.keepaliveObserved hooks pid) :=
  pair (source_state (CompleteTransmit.keepalive pid)) (CompleteNative.keepalive_erases pid)
    (CompleteNative.keepalive pid)

theorem transmit (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateChecked (Driver.transmitObserved hooks family addr packets mtu) :=
  pair (source_state (CompleteTransmit.transmit family addr packets mtu))
    (CompleteNative.transmit_erases family addr packets mtu) (CompleteNative.transmit family addr packets mtu)

theorem handshake : StateChecked (Driver.handshakeObserved hooks) :=
  pair (CompleteHandshakeWorker.session_worker Safe account_safe (Driver.keepaliveObserved hooks)
      (fun pid => source_state (CompleteTransmit.keepalive pid)))
    CompleteNative.handshake_erases CompleteNative.handshake

theorem release (peer : Option PeerId) : StateChecked (hooks.peerRelease peer) :=
  pair (CompleteSource.original peer Safe account_safe) (CompleteNative.release_erases peer)
    (AllocatedFrames.release peer)

theorem down : StateChecked (Driver.downObserved hooks) :=
  pair (CompleteLifecycle.down Safe account_safe) CompleteNative.down_erases CompleteNative.down

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
