import Leanux.Proofs.WG.Roaming.RemotePollModel
import Leanux.Proofs.WG.Roaming.RemoteSilentSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemotePoll
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged

abbrev Retained := RemoteSilent.Retained
def ProductRetained (entry : RemoteMap) (w : World) : Prop := Retained entry w.wg
def localCause (e : RxJoint.Event) : PeerId→Nat×Nat×Nat×Nat→Prop :=
  rxCause (RxHistory.promote e)

def Covered {E : Type} (entry : RemoteMap)
    (cause : E→PeerId→Nat×Nat×Nat×Nat→Prop) (h : List E) (w : World) : Prop :=
  RemoteCovered entry cause h (destinationAt w.wg)

end Leanux.Proofs.WG.Roaming.RemotePoll
