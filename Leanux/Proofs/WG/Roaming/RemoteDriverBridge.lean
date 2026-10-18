import Leanux.Proofs.WG.Roaming.RemoteConfigurationBridge
import Leanux.Proofs.WG.Roaming.ReceiveStepRemoteCaptureSource
import Leanux.Proofs.WG.Roaming.RemoteOriginSource
import Leanux.Proofs.WG.Roaming.RemotePollModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDriver
open Leanux Leanux.WG Noise Queues Leanux.Proofs.Logged

/-- Internal execution evidence. Public statements project these witnesses;
the observer executes each original caller only once. -/
inductive Event where
  | rx (event : RxHistory.Event)
  | receive (run : RunWitness Bool)
  | endpoint (run : RemoteConfiguration.EndpointRun)
  | birth (receipt : PeerCreateReceipt)

def rxEvent : Event → Option RxHistory.Event
  | .rx event => some event
  | _ => none

def EventValid : Event → Prop
  | .rx _ => True
  | .receive run => run.Valid (liftWG receiveStep)
  | .endpoint run => run.Valid
  | .birth receipt => DriverTags.PeerCreateValid receipt

def Cause : Event → PeerId → Nat × Nat × Nat × Nat → Prop
  | .rx event, pid, remote => RemotePoll.rxCause event pid remote
  | .receive run, pid, remote =>
    ∃ observation : ReceiveStepRemote.Observation,
      ReceiveStepRemote.Matches run observation ∧ observation.Cause pid remote
  | .endpoint run, pid, remote =>
    run.peer = pid ∧ destination run.endpoint = remote ∧
      (run.endpoint.family = AF_INET ∨ run.endpoint.family = AF_INET6)
  | .birth _, _, _ => False

def Safe (events : List Event) : Prop := RemoteHistoryValid EventValid events

def NativeInv (entry : RemoteMap) (events : List Event) (g : WGWorld) : Prop :=
  RemoteOrigin.Inv entry Cause EventValid events (destinationAt g)

def Inv (entry : RemoteMap) (events : List Event) (w : World) : Prop :=
  NativeInv entry events w.wg

def focus {α : Type} (action : RxHistory.Obs α) : PrefixM Event α :=
  focusPrefix Event.rx rxEvent action

end Leanux.Proofs.WG.Roaming.RemoteDriver
