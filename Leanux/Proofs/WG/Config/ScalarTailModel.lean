import Leanux.Proofs.WG.Config.ScalarFinishModel
import Leanux.Proofs.WG.Config.ScalarPrefixModel

/-! A negative original tail result exits before keepalive setup. A nonnegative result completes the original finish path. Endpoint effects use the actual setter equality and attribute decoding, including ignored encodings. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarTail
open Leanux Leanux.WG Noise Std.Do
open Queues Queues.RxCredits Leanux.Proofs.Framing Lifetimes
open PeerScalarRetention ScalarFinish

def tailCell (attrs : PeerAttrs) (ret : Int) (expected : Cell) : Cell :=
  if ret<0 then expected else finishCell attrs expected

def prefixCell (p : Peer) (psk : Option Key) (endpoint : Option EndpointAttr) : Cell :=
  cell (ScalarPrefix.effectPeer p psk endpoint none)

end Leanux.Proofs.WG.Config.ScalarTail
