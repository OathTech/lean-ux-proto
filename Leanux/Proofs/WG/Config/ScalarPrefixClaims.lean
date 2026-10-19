import Leanux.Proofs.WG.Config.ScalarPrefixSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarPrefix
open Leanux Leanux.WG Noise Std.Do

def Matches (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (initial : Campaign2.Snapshot)
    (result : Inspection) : Prop :=
  ∃ g ambient, Campaign2.snapshot g ambient=initial ∧
    inspection attrs peer flags psk pid g ambient=result

theorem original_update_inspection (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (keep : flags &&& WGPEER_F_REMOVE_ME = 0)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) :
    Campaign2.Returns (inspect attrs peer flags psk pid)
      (fun s=>s.wg.device=some d)
      (fun result s=>Matches attrs peer flags psk pid s result ∧
        Facts attrs psk pid d p s result) := by
  intro g ambient device
  exact ⟨inspection attrs peer flags psk pid g ambient,g,ambient,rfl,
    ⟨g,ambient,rfl,rfl⟩,inspection_facts attrs peer flags psk pid keep d p resident g ambient device⟩

theorem original_update_outcome (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (keep : flags &&& WGPEER_F_REMOVE_ME = 0)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) :
    Campaign2.Observes (peerConfigUpdateSource attrs peer flags psk pid)
      (fun s=>s.wg.device=some d)
      (fun initial outcome=>∃result,Matches attrs peer flags psk pid initial result ∧
        result.outcome=outcome ∧ Facts attrs psk pid d p initial result) := by
  intro g ambient device
  exact ⟨inspection attrs peer flags psk pid g ambient,⟨g,ambient,rfl,rfl⟩,
    inspection_outcome attrs peer flags psk pid g ambient,
    inspection_facts attrs peer flags psk pid keep d p resident g ambient device⟩

end Leanux.Proofs.WG.Config.ScalarPrefix
