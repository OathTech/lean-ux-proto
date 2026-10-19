import Leanux.Proofs.WG.Progress.PeerCreationFiniteCoreSource
import Leanux.Proofs.WG.Queues.BaseCreation

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.PeerFinite
open Leanux Leanux.WG
open Leanux.Proofs.WG.Queues.RxCredits

theorem finishWith_source (pid : PeerId) (key : Key) (psk : Option Key) :
    BaseCreation.finish pid key psk = finishWith WG.handshakeInit pid key psk := rfl

theorem createWith_source (key : Key) (psk : Option Key) :
    WG.peerCreate key psk =
      createWith (hiddenAlloc .kmemCacheZallocPeer) BaseCreation.finish key psk := by
  exact BaseCreation.peerCreate_factor key psk

end Leanux.Proofs.WG.Progress.PeerFinite
