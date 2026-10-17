import Leanux.Proofs.WG.Config.SocketReadbackDrainSource
import Leanux.Proofs.WG.Config.ClaimView

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Two actual fixed-capacity socket chunks serialize one peer's finite IPv4
list and are drained and coalesced by the original getter. The continuation
ID must not occur in the first chunk's prefix; duplicates elsewhere are
serialized in order. No reachability or multi-peer pagination is asserted. -/
theorem socketReadback_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (front : List NodeId) (b : NodeId) (tail : List NodeId)
    (sock : NlSock) (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = front ++ b :: tail) (nonempty : front ≠ [])
    (absent : b ∉ front) (readable : Ipv4Residents d nodes (front ++ b :: tail))
    (endpoint : p.endpoint = none)
    (firstFits : devicePrefixSpace d + 140 + 28 * front.length ≤ NLMSG_GOODSIZE)
    (firstFull : NLMSG_GOODSIZE < devicePrefixSpace d + 140 + 28 * (front.length + 1))
    (lastFits : devicePrefixSpace d + 44 + 28 * (b :: tail).length + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun q s => q = .ok (suffixJson d p nodes (front ++ b :: tail)) ∧
        s.wg.device = some d ∧ s.wg.nlSock7 = socketReadbackFinal sock d) := by
  have firstReadable : Ipv4Residents d nodes (front ++ [b]) := by
    intro id member
    apply readable id
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact List.mem_append_left _ member
    · simp
  have lastReadable : Ipv4Residents d nodes (b :: tail) := by
    intro id member
    exact readable id (List.mem_append_right _ member)
  have len : 0 < front.length := List.length_pos_iff.mpr nonempty
  have first := socketFirstCall_returns pid d p nodes front b tail peers resident
    listed nonempty firstReadable endpoint firstFits firstFull
  have last := socketLastCall_returns pid d p nodes front b tail peers resident
    listed absent lastReadable (by omega) lastFits
  have start := netlinkDumpStart_front d p nodes front b sock idle first
  have drain := getterDrain_two d p nodes front b tail sock empty endpoint lastFits last
  have whole : Returns (wgGetDevice (byIndex d))
      (fun w => w.dev = some d ∧ w.nlSock7 = sock ∧ selectsDevice w d)
      (fun q w => q = .ok (suffixJson d p nodes (front ++ b :: tail)) ∧
        w.dev = some d ∧ w.nlSock7 = socketReadbackFinal sock d) := by
    rw [wgGetDevice_source]
    exact returns_bind _ _ start (fun _ => drain)
  exact whole

end Leanux.Proofs.WG.Config
