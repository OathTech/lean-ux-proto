import Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffectsSource
import Leanux.Proofs.WG.TransmitSecurity.DriverSource

/-! Exact insertion sites in the current shared driver. Each equality preserves
the original guards and failed prefixes. The direct transmit equality is used
only at the supplied syscall/batch callback, never at stack-reply transmission. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Queues Configuration Packets Lifetimes TransmitSecurity

theorem peerFinish_factor (hooks : Driver.Hooks E) (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    Driver.configTailFinish hooks attrs peer pid ret =
      peerFinishObserved (Driver.fixtureOps hooks) (Driver.stagingObserved hooks) (Driver.keepaliveObserved hooks)
        (Driver.configOut hooks) attrs peer pid ret := by
  rfl

theorem open_factor (hooks : Driver.Hooks E) :
    Driver.openObserved hooks =
      openObserved (Driver.fixtureOps hooks) (Driver.stagingObserved hooks) (Driver.keepaliveObserved hooks) := by
  rfl

theorem identity_factor (hooks : Driver.Hooks E) (attrs : DeviceAttrs) :
    Driver.configKey hooks attrs =
      deviceKeyWith (fun {_} a => liftWGPrefix a) (fun key => liftWGPrefix (pubkeyLookup key))
        hooks.peerRelease (Driver.removeObserved hooks)
        (fun pid => liftWGPrefix (precomputeStaticStatic pid))
        (fun pid => liftWGPrefix (expireCurrentPeerKeypairs pid))
        (fun pid => runWith (Driver.fixtureOps hooks) (.identityConfiguration attrs pid) (Driver.stagingObserved hooks pid))
        (Driver.configPeers hooks attrs) attrs := by
  rfl

theorem syscall_factor (hooks : Driver.Hooks E) (family addr : Nat)
    (payload : List UInt8) (opts : Env.XmitOpts) :
    Driver.syscallXmitObserved hooks family addr payload opts =
      syscallXmitWith Driver.multicastObserved
        (fun family addr packets mtu => liftWGObserver
          (runWith (Driver.fixtureOps hooks) (.transmit family addr packets mtu)
            (Driver.transmitObserved hooks family addr packets mtu))) family addr payload opts := by
  rfl

theorem batchItem_factor (hooks : Driver.Hooks E) (device : Device)
    (cqes : List Int) (item : Env.BatchItem) :
    Driver.batchItemObserved hooks device cqes item =
      batchItemWith (Driver.receiveEntryObserved hooks) (Driver.inlinePollObserved hooks) Driver.multicastObserved
        (fun family addr packets mtu => liftWGObserver
          (runWith (Driver.fixtureOps hooks) (.transmit family addr packets mtu)
            (Driver.transmitObserved hooks family addr packets mtu))) device cqes item := by
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffects
