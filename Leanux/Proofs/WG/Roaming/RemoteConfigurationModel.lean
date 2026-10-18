import Leanux.Proofs.WG.Roaming.RemoteControlModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteConfiguration
open Leanux Leanux.WG

structure EndpointReceipt where
  peer : PeerId
  endpoint : Endpoint
  before : Campaign2.Snapshot
  after : Campaign2.Snapshot
def EndpointReceipt.Effect (r : EndpointReceipt) : Prop :=
  remoteMap r.after = RemoteControl.setterRemotes (remoteMap r.before) r.peer r.endpoint

end Leanux.Proofs.WG.Roaming.RemoteConfiguration
