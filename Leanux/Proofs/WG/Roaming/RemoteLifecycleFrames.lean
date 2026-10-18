import Leanux.Proofs.WG.Roaming.RemoteDriverSource
import Leanux.Proofs.WG.Roaming.RemotePollFrames
import Leanux.Proofs.WG.Index.LifecycleEnvironmentRuleSource
import Leanux.Proofs.WG.Config.DumpInvariantSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming.RemoteLifecycle
open Leanux Leanux.WG Noise Lifetimes Queues Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open RemoteSilent

theorem link_remotes (g : WGWorld) :
    responseEndpointMap (linkView g).dev = responseEndpointMap g.dev := by
  funext pid
  cases device : g.dev <;> simp [linkView,linkStore,linkDevice,wgStoreView,responseEndpointMap,device]

end Leanux.Proofs.WG.Roaming.RemoteLifecycle
