import Leanux.Proofs.WG.Config.SocketReadbackSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem socketFirstCall_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (front : List NodeId) (b : NodeId) (tail : List NodeId)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = front ++ b :: tail) (nonempty : front ≠ [])
    (readable : Ipv4Residents d nodes (front ++ [b])) (endpoint : p.endpoint = none)
    (fits : devicePrefixSpace d + 140 + 28 * front.length ≤ NLMSG_GOODSIZE)
    (short : NLMSG_GOODSIZE < devicePrefixSpace d + 140 + 28 * (front.length + 1)) :
    Returns (wgGetDeviceDump { hasWg := true } 0 {}) (fun w => w.dev = some d)
      (fun q w => q = socketFirstCall d p nodes front b ∧ w.dev = some d) := by
  have len : 0 < front.length := List.length_pos_iff.mpr nonempty
  have ht := dumpTail_front d nodes p front b tail listed nonempty readable endpoint
    { hasWg := true } { room := NLMSG_GOODSIZE - devicePrefixSpace d }
    rfl rfl (by dsimp; omega) (by dsimp; omega)
  have hp := multipart_getter_returns pid d p { hasWg := true }
    { room := NLMSG_GOODSIZE - devicePrefixSpace d } _ resident ((returns_iff _ _ _).mpr ht)
  have result := deviceDump_single_contract pid d { hasWg := true }
    { hasWg := true, nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq }
    0 (NLMSG_GOODSIZE - devicePrefixSpace d - (140 + 28 * front.length))
    (socketFirstPeer p nodes front) true peers rfl rfl (.inl rfl) (by omega) hp
  simpa [socketCallbackResult, socketFirstCall, Nat.sub_sub, Nat.add_assoc] using result

theorem socketLastCall_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (front : List NodeId) (b : NodeId) (tail : List NodeId)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = front ++ b :: tail) (absent : b ∉ front)
    (readable : Ipv4Residents d nodes (b :: tail))
    (headerFits : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (fits : devicePrefixSpace d + 44 + 28 * (b :: tail).length + 20 ≤ NLMSG_GOODSIZE) :
    Returns (wgGetDeviceDump
      { hasWg := true, nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq }
      d.deviceUpdateGen {}) (fun w => w.dev = some d)
      (fun q w => q = socketLastCall d p nodes (b :: tail) ∧ w.dev = some d) := by
  have ht := dumpTail_after_front d nodes p front b tail listed absent readable
    { hasWg := true, nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq }
    { room := NLMSG_GOODSIZE - devicePrefixSpace d } rfl rfl (by simp only [List.length_cons] at fits ⊢; omega)
  have hp := multipart_getter_returns pid d p
    { hasWg := true, nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq }
    { room := NLMSG_GOODSIZE - devicePrefixSpace d } _ resident ((returns_iff _ _ _).mpr ht)
  have result := deviceDump_single_contract pid d
    { hasWg := true, nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq }
    { hasWg := true } d.deviceUpdateGen
    (NLMSG_GOODSIZE - devicePrefixSpace d - (44 + 28 * (b :: tail).length))
    (suffixLast p nodes (b :: tail)) false peers rfl rfl (.inr rfl) headerFits hp
  simpa [socketCallbackResult, socketLastCall, Nat.sub_sub, Nat.add_assoc] using result

end Leanux.Proofs.WG.Config
