import Leanux.Proofs.WG.Noise.PeerCreationRuleSource
import Leanux.Proofs.WG.Roaming.RemoteBirthFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteBirth
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits Leanux.Proofs.Framing Std.Do

theorem peerCreate_remotes (key : Key) (psk : Option Key) (entry : RemoteMap) :
    Ensures (peerCreate key psk) (fun g => destinationAt g = entry)
      (fun result g => destinationAt g = birthRemotes entry result) := by
  let P : WGWorld→Prop := fun g=>destinationAt g=entry
  let Q := fun (result : Except Int PeerId) (g : WGWorld)=>
    destinationAt g=birthRemotes entry result
  refine (Noise.ensures_iff (peerCreate key psk) P Q).mpr ?_
  apply peerCreate_rule key psk P (fun pid=>Q (.ok pid)) Q
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro g a result final b pre run
    cases device : g.dev <;> simp [getDev,device,invariant,AmbientM.invariant] at run
    · cases run
    · obtain ⟨⟨rfl,rfl⟩,rfl⟩:=run
      exact pre
  · intro g pre
    exact pre
  · intro pid
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro g a result final b pre run
    rw [Peers.peerCreateCore_run] at run
    cases run
    change destinationAt (Peers.creationCoreWorld g pid key)=birthRemotes entry (.ok pid)
    rw [creationCore_remotes,pre]
  · intro pid
    exact (finish_remotes pid key psk (birthRemotes entry (.ok pid)))

theorem receipt_effect (r : PeerCreateReceipt) (valid : DriverTags.PeerCreateValid r) :
    BirthRemoteEffect r := by
  refine ⟨valid.effect.1,?_⟩
  obtain ⟨g,a,final,b,beforeEq,afterEq,run⟩ := valid
  rw [afterEq,beforeEq]
  exact peerCreate_remotes r.publicKey r.presharedKey (destinationAt g)
    g a r.result final b rfl run

end Leanux.Proofs.WG.Roaming.RemoteBirth
