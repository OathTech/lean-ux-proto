import Leanux.Proofs.WG.Roaming.RemoteBirthSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteBirth
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits Leanux.Proofs.Framing Std.Do

theorem peerCreate_effect (key : Key) (psk : Option Key) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (peerCreate key psk) (fun s => s = entry)
      (fun result after => BirthRemoteEffect ⟨key,psk,entry,result,after⟩) := by
  intro g a result final b pre run
  exact receipt_effect _ ⟨g,a,final,b,pre.symm,rfl,run⟩

end Leanux.Proofs.WG.Roaming.RemoteBirth
