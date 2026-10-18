import Leanux.Proofs.WG.Index.ConfigurationDeviceSource
import Leanux.Proofs.WG.Index.InitiationIndexSource
import Leanux.Proofs.WG.Index.RetirementClearWorkerEffects
import Leanux.Proofs.WG.Noise.DriverTagControlSource
import Leanux.Proofs.WG.Queues.DeviceAuxEntry
import Leanux.Proofs.WG.Index.LifecycleRuleSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.LifecycleIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits Queues.RxCredits.DurableHolders
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open ConfigurationIndex

theorem reset_fields (pid : PeerId) : SameView fields (resetLastSentHandshake pid) := by
  have factor : resetLastSentHandshake pid = (do
      let now ← hiddenClock64 .resetLastSent
      modifyPeer pid (fun p => {p with lastSentHandshake :=
        now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64})) := rfl
  rw [factor]
  have clock : SameView fields (hiddenClock64 .resetLastSent : WG.M Int64) := by
    intro initial
    exact hoare_liftAmbient _ _
  exact clock.bind (fun _ => modifyPeer_fields pid _ (fun _ => rfl))

theorem link_fields (w : WGWorld) :
    (linkView w).dev.map deviceFields=fields w := by
  simp only [linkView,linkStore,linkDevice,wgStoreView,fields,deviceFields,
    senderDeviceCell,Option.map_map,Function.comp_def]
  rfl

end Leanux.Proofs.WG.Index.LifecycleIndex
