import Leanux.Proofs.WG.Noise.MacSource

/-! Response-prefix tag frames. The MAC contract is a local variant of
Keypairs.WGFrames.addMacToPacket_spec; clock and timestamp facts project
existing ambient/peer-update contracts. -/
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing

theorem addMacToPacket_spec_tagMap_variant (pid : PeerId) (msg : List UInt8) (entry : Option Device) :
    Ensures (addMacToPacket pid msg)
      (fun (g : WGWorld) => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  apply addMacToPacket_preserves pid msg
    (fun g => responseTagMap g.dev = responseTagMap entry)
  intro p
  intro g a x v b pre run
  let updated : Peer := {p with lastMac1Sent := blake2s 16 p.cookieMac1Key (msg.take (msg.length - 32)), haveSentMac1 := true}
  change Except.ok (((), {g with dev := g.dev.map (fun (d : Device) => {d with peers := d.peers.insert pid updated})}), a) = _ at run
  cases run
  apply Eq.trans _ pre.1
  funext target
  cases hd : g.dev with
  | none => simp [peerAt, hd] at pre
  | some d =>
    have resident : d.peers[pid]? = some p := by simpa [peerAt,hd] using pre.2
    by_cases same : pid = target
    · subst target
      simp [updated,responseTagMap,resident]
    · simp [updated,responseTagMap,Std.TreeMap.getElem?_insert,same]

end Leanux.Proofs.WG.Noise

namespace Leanux.Proofs.WG.Noise.ResponseCaller
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem clock_tag_frame (site : HiddenSite) (g : WGWorld) (ambient : Ambient)
    (now : Int64) (final : WGWorld) (after : Ambient)
    (run : (((hiddenClock64 site : WG.M Int64).run g).run ambient) =
      .ok ((now, final), after)) : responseTagMap final.dev = responseTagMap g.dev := by
  exact ((Noise.ensures_iff _ _ _).mpr
    (hoare_liftAmbient (AmbientM.hiddenClock64 site) (fun w => responseTagMap w.dev = responseTagMap g.dev)))
    g ambient now final after rfl run

theorem lastSent_tag_frame (pid : PeerId) (now : Int64)
    (g : WGWorld) (ambient : Ambient) (x : Unit) (final : WGWorld) (after : Ambient)
    (run : (((do let p ← getPeer pid
                 setPeer pid {p with lastSentHandshake := now}) : WG.M Unit).run g).run ambient =
      .ok ((x, final), after)) : responseTagMap final.dev = responseTagMap g.dev := by
  have h := modifyPeer_spec_creationTagMap_variant g.dev pid
    (fun p => {p with lastSentHandshake := now}) id (fun _ => rfl)
    g ambient x final after rfl run
  funext target
  simpa only [id_eq, ite_self] using h target

end Leanux.Proofs.WG.Noise.ResponseCaller
