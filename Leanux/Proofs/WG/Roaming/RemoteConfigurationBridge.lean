import Leanux.Proofs.WG.Roaming.RemoteConfigurationModel
import Leanux.Proofs.WG.Roaming.RemoteBirthClaims
import Leanux.Proofs.WG.Roaming.RemoteControlSource
import Leanux.Proofs.Logged.NativeCapture

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteConfiguration
open Leanux Leanux.WG Noise Lifetimes Queues Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do

structure EndpointRun where
  peer : PeerId
  endpoint : Endpoint
  run : WGRunWitness Unit

def EndpointRun.projects (r : EndpointRun) : EndpointReceipt :=
  ⟨r.peer,r.endpoint,Campaign2.snapshot r.run.before r.run.ambientBefore,
    Campaign2.snapshot r.run.after r.run.ambientAfter⟩

def EndpointRun.Valid (r : EndpointRun) : Prop :=
  r.run.Valid (setPeerEndpoint r.peer r.endpoint)
theorem EndpointRun.effect (r : EndpointRun) (valid : r.Valid) : r.projects.Effect :=
  RemoteControl.setPeerEndpoint_all_remotes r.peer r.endpoint (destinationAt r.run.before)
    r.run.before r.run.ambientBefore r.run.value r.run.after r.run.ambientAfter rfl valid

def birthReceipt (key : Key) (psk : Option Key)
    (r : WGRunWitness (Except Int PeerId)) : PeerCreateReceipt :=
  ⟨key,psk,Campaign2.snapshot r.before r.ambientBefore,r.value,
    Campaign2.snapshot r.after r.ambientAfter⟩

theorem birthReceipt_valid (key : Key) (psk : Option Key)
    (r : WGRunWitness (Except Int PeerId)) (valid : r.Valid (peerCreate key psk)) :
    DriverTags.PeerCreateValid (birthReceipt key psk r) :=
  ⟨r.before,r.ambientBefore,r.after,r.ambientAfter,rfl,rfl,valid⟩

theorem birthReceipt_effect (key : Key) (psk : Option Key)
    (r : WGRunWitness (Except Int PeerId)) (valid : r.Valid (peerCreate key psk)) :
    RemoteBirth.BirthRemoteEffect (birthReceipt key psk r) :=
  RemoteBirth.receipt_effect _ (birthReceipt_valid key psk r valid)

end Leanux.Proofs.WG.Roaming.RemoteConfiguration
