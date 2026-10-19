import Leanux.Proofs.WG.Config.OwnerDriverBridge
import Leanux.Proofs.WG.Index.ReachedRunnerFrames
import Leanux.Proofs.Framing.EnvOperations

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerDriver
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Leanux.Proofs.WG.Config.OwnerConfiguration

theorem optional_store (w v : WGWorld) (same : wgStoreView v=wgStoreView w)
    (pre : OptionalReady w) : OptionalReady v := by
  have device : v.dev=w.dev := congrArg WGStoreView.dev same
  intro d present
  exact pre d (device.symm.trans present)

theorem store (h : List RxHistory.Event) (w v : World)
    (same : wgStoreView v.wg=wgStoreView w.wg) (pre : Inv h w) : Inv h v :=
  ⟨Index.Reached.anyEntry_store h w v same pre.1,optional_store w.wg v.wg same pre.2⟩

theorem mtu_base (n : Nat) :
    SameView (fun w : World=>BaseCoherence.view w.wg) (Env.setMtu n) := by
  apply (setMtu_sameEnvScalar n).of_factor
    (fun s : ProductStore43=>BaseCoherence.view {dev:=s.2.2.2.dev})
  intro w
  simp only [BaseCoherence.view,BaseCoherence.slots,BaseCoherence.rows,
    envScalarView,envScalarStore,productStoreView,wgStoreView,
    envScalarDevice,Option.map_map,Function.comp_def]

end Leanux.Proofs.WG.Config.OwnerDriver
