import Leanux.Proofs.WG.Config.WeightedStartModel
import Leanux.Proofs.WG.Config.MixedDumpCallbackSource
import Leanux.Proofs.WG.Config.PaginationFirstSource
import Leanux.Proofs.WG.Config.EndpointPaginationTransportSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The original first callback on every readable finite list, whether empty,
complete or split. Only a nonempty input needs room for the allowed-IP nest;
there is no assumption that the first node fits. -/
theorem mixedFirstCall_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (nest : ids ≠ [] → devicePrefixSpace d + (peerFixedSpace p + 4) ≤ NLMSG_GOODSIZE) :
    Returns (wgGetDeviceDump {hasWg := true} 0 {}) (fun g => g.dev = some d)
      (fun result g => result = mixedFirstCall d p nodes ids ∧ g.dev = some d) := by
  cases ids with
  | nil => exact socketEmptyFirstCall_returns pid d p peers resident listed header
  | cons first rest =>
    have nesting := nest (by simp)
    have facts := weightedPrefix_spec nodes
      (NLMSG_GOODSIZE - devicePrefixSpace d - (peerFixedSpace p + 4)) (first :: rest)
    cases plan : weightedPrefix nodes
      (NLMSG_GOODSIZE - devicePrefixSpace d - (peerFixedSpace p + 4)) (first :: rest) with
    | mk front remaining =>
      rw [plan] at facts
      dsimp only at facts
      have fits : devicePrefixSpace d + (peerFixedSpace p + 4) + dumpNodesSpace nodes front ≤ NLMSG_GOODSIZE := by
        have h := facts.2.1
        omega
      cases remaining with
      | nil =>
        have decomp : front = first :: rest := by simpa using facts.1
        let skb : NlSkb := {room := NLMSG_GOODSIZE - devicePrefixSpace d}
        have selected : p.allowedipsList.dropWhile (· != first) = first :: rest := by simp [listed]
        have allowed := dumpAllowed_weighted_all d nodes p {hasWg := true} skb
          {skb with room := skb.room - peerFixedSpace p} (hexKey p.remoteStatic) (peerFixedAttrs p)
          first (first :: rest) readable selected (by simp) (.inl rfl)
          (by dsimp [skb]; rw [decomp] at fits; omega)
        have fixed := dumpTail_first_allowed d p {hasWg := true} skb _ rfl
          (by dsimp [skb]; omega) (by simpa only [listed, List.head?_cons] using allowed)
        have getter := multipart_getter_returns pid d p _ _ _ resident fixed
        have call := deviceDump_single_contract pid d {hasWg := true} {hasWg := true} 0
          (NLMSG_GOODSIZE - (devicePrefixSpace d + (peerFixedSpace p + 4) + dumpNodesSpace nodes (first :: rest)))
          {publicKey := hexKey p.remoteStatic,
           attrs := peerFixedAttrs p ++ [("allowed_ips", Json.arr (dumpNodeJsons nodes (first :: rest)))]}
          false peers rfl rfl (.inl rfl) header
          (by simpa [skb, Nat.sub_sub, Nat.add_assoc] using getter)
        simpa [mixedFirstCall, plan, decomp] using call
      | cons next tail =>
        have decomp : front ++ next :: tail = first :: rest := facts.1
        have reads : ∀ id ∈ front ++ [next], d.nodes[id]? = some (nodes id) := by
          intro id member
          apply readable id
          rw [← decomp]
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
          rcases member with member | same
          · exact .inl member
          · exact .inr (.inl same)
        have short := facts.2.2 next tail rfl
        have call := mixedFirstSplit_returns pid d p nodes front next tail peers resident
          (by rw [decomp]; exact listed) reads header fits (by omega)
        simpa [mixedFirstCall, plan] using call

/-- Actual interface selection and dump start feed the derived first callback
to the original socket. Completion can append DONE immediately or leave it
for a later receive; an initially empty allowed-IP list is not an exception. -/
theorem netlinkDumpStart_mixed_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (nest : ids ≠ [] → devicePrefixSpace d + (peerFixedSpace p + 4) ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Returns (netlinkDumpStart 7 (byIndex d))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
      (fun _ g => g.dev = some d ∧ g.nlSock7 = mixedStartedSocket sock (mixedFirstCall d p nodes ids)) := by
  have callback := mixedFirstCall_returns pid d p nodes ids peers resident listed readable header nest
  have shape := mixedFirstCall_shape d p nodes ids
  by_cases completed : (mixedFirstCall d p nodes ids).ret = 0
  · simpa [mixedStartedSocket, completed] using
      netlinkDumpStart_completed_empty d sock (mixedFirstCall d p nodes ids) idle empty completed shape.1 callback
  · have positive : 0 < (mixedFirstCall d p nodes ids).ret := by omega
    simpa [mixedStartedSocket, completed] using
      netlinkDumpStart_more_empty d sock (mixedFirstCall d p nodes ids) idle empty positive callback

end Leanux.Proofs.WG.Config
