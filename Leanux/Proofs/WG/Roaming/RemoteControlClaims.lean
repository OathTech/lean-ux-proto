import Leanux.Proofs.WG.Roaming.RemoteControlSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteControl
open Leanux Leanux.WG

theorem setPeerEndpoint_effect (entry : Campaign2.Snapshot)
    (pid : PeerId) (endpoint : Endpoint) :
    Campaign2.Ensures (setPeerEndpoint pid endpoint)
      (fun s => remoteMap s = remoteMap entry)
      (fun _ s => remoteMap s = setterRemotes (remoteMap entry) pid endpoint) :=
  setPeerEndpoint_all_remotes pid endpoint (remoteMap entry)

theorem consumeDataDone_effect (entry : Campaign2.Snapshot)
    (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Campaign2.Ensures (consumeDataDone pid pkt endpoint)
      (fun s => remoteMap s = remoteMap entry)
      (fun _ s => RemoteRetained (setterRemotes (remoteMap entry) pid endpoint) (remoteMap s)) :=
  consumeDataDone_all_remotes (remoteMap entry) pid pkt endpoint

end Leanux.Proofs.WG.Roaming.RemoteControl
