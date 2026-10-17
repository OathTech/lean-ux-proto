import Leanux.Proofs.WG.Config.MixedDumpScanSource
import Leanux.Proofs.WG.Config.EndpointPaginationFirstSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The actual initial callback emits all fixed peer attributes, then the exact
weighted fitting prefix. The prefix may be empty; this is a DATA split, not
cancelled nesting or a theorem about the full getter's progress. -/
theorem mixedFirstSplit_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (front : List NodeId) (next : NodeId) (tail : List NodeId)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = front ++ next :: tail)
    (readable : ∀id ∈ front ++ [next], d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (fits : devicePrefixSpace d + (peerFixedSpace p + 4) + dumpNodesSpace nodes front ≤ NLMSG_GOODSIZE)
    (short : NLMSG_GOODSIZE < devicePrefixSpace d + (peerFixedSpace p + 4) +
      dumpNodesSpace nodes front + dumpNodeSpace (nodes next)) :
    Returns (wgGetDeviceDump {hasWg := true} 0 {}) (fun g => g.dev = some d)
      (fun result g => result = socketCallbackResult d
        {hasWg := true,nextAllowedip := some next,allowedipsSeq := d.peerAllowedips.seq}
        (NLMSG_GOODSIZE - (devicePrefixSpace d + (peerFixedSpace p + 4) + dumpNodesSpace nodes front))
        {publicKey := hexKey p.remoteStatic,
         attrs := peerFixedAttrs p ++ [("allowed_ips",Json.arr (dumpNodeJsons nodes front))],split := true}
        true ∧ g.dev = some d) := by
  let skb : NlSkb := {room := NLMSG_GOODSIZE - devicePrefixSpace d}
  let start := (front ++ next :: tail).head!
  have selected : p.allowedipsList.dropWhile (· != start) = front ++ next :: tail := by
    cases front <;> simp [listed,start,List.head!]
  have head : p.allowedipsList.head? = some start := by
    cases front <;> simp [listed,start,List.head!]
  have allowed := dumpAllowed_weighted_split d nodes p {hasWg := true} skb
    {skb with room := skb.room - peerFixedSpace p} (hexKey p.remoteStatic) (peerFixedAttrs p)
    start front next tail readable selected (.inl rfl)
    (by dsimp [skb]; omega) (by dsimp [skb]; omega)
  have first := dumpTail_first_allowed d p {hasWg := true} skb _ rfl (by dsimp [skb]; omega)
    (by simpa only [head] using allowed)
  have getter := multipart_getter_returns pid d p _ _ _ resident first
  exact deviceDump_single_contract pid d {hasWg := true}
    {hasWg := true,nextAllowedip := some next,allowedipsSeq := d.peerAllowedips.seq}
    0 _ _ true peers rfl rfl (.inl rfl) header
    (by simpa [skb,Nat.sub_sub,Nat.add_assoc] using getter)

end Leanux.Proofs.WG.Config
