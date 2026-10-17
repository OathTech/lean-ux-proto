import Leanux.Proofs.WG.Config.EndpointPaginationModel
import Leanux.Proofs.WG.Config.PaginationFirstSource
import Leanux.Proofs.WG.Config.SocketReadbackSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The original full-attribute prefix passes its actual remaining room and
attributes to the original allowed-IP continuation, for every endpoint value. -/
theorem dumpTail_first_allowed (d : Device) (p : Peer) (ctx : DumpCtx) (skb : NlSkb)
    (expected : PeerDumpResult) (fresh : ctx.nextAllowedip = none) (room : 168 ≤ skb.room)
    (tail : Returns (getPeerDumpAllowedSource p ctx skb {skb with room := skb.room - peerFixedSpace p}
      (hexKey p.remoteStatic) (peerFixedAttrs p) p.allowedipsList.head?)
      (fun g => g.dev = some d) (fun result g => g.dev = some d ∧ result = expected)) :
    Returns (getPeerDumpTailSource p ctx skb) (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧ result = expected) := by
  have r4 : ¬ skb.room < 4 := by omega
  have r40 : ¬ skb.room - 4 < 36 := by omega
  have r76 : ¬ skb.room - 40 < 36 := by omega
  have r96 : ¬ skb.room - 76 < 20 := by omega
  have r104 : ¬ skb.room - 96 < 8 := by omega
  have r116 : ¬ skb.room - 104 < 12 := by omega
  have r128 : ¬ skb.room - 116 < 12 := by omega
  have r136 : ¬ skb.room - 128 < 8 := by omega
  have r156 : ¬ skb.room - 136 < 20 := by omega
  have r168 : ¬ skb.room - 136 < 32 := by omega
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision,outcome,netRx := a.netRxSection}}
  let markedPrefix := mark (mark (mark (mark (mark (mark (mark (mark (mark ambient
    .getPeerNoNest false) .getPeerPubkeyFail false) .getPeerFirst true)
    .getPeerPskFail false) .getPeerPutHandshake false) .getPeerPutKeepalive false)
    .getPeerPutTx false) .getPeerPutRx false) .getPeerPutProto false
  let family := (p.endpoint.map (·.family)).getD 0
  let ep := mark markedPrefix .getPeerEp4 (family == AF_INET)
  let before := mark (if family = AF_INET then ep else mark ep .getPeerEp6 (family == AF_INET6))
    .getPeerEpFail false
  obtain ⟨result,final,after,run,deviceOut,value⟩ := tail g before device
  refine ⟨result,final,after,?_,deviceOut,value⟩
  have source : ((getPeerDumpTailSource p ctx skb).run g).run ambient =
      ((getPeerDumpAllowedSource p ctx skb {skb with room := skb.room - peerFixedSpace p}
        (hexKey p.remoteStatic) (peerFixedAttrs p) p.allowedipsList.head?).run g).run before := by
    by_cases ep4 : (p.endpoint.map (·.family)).getD 0 = AF_INET <;>
      by_cases ep6 : (p.endpoint.map (·.family)).getD 0 = AF_INET6
    all_goals simp [getPeerDumpTailSource,fresh,branch,AmbientM.branch,NlSkb.put,nlaTotal,
      Nat.sub_sub,r4,r40,r76,r96,r104,r116,r128,r136,r156,r168,ep4,ep6,
      peerFixedSpace,peerFixedAttrs,before,ep,markedPrefix,family,mark]
    all_goals generalize getPeerDumpAllowedSource = allowed
    all_goals cases p.endpoint <;> rfl
  exact source.trans run

/-- A first page with complete endpoint fields splits exactly at its next
un-emitted IPv4 node. No callback outcome is assumed. -/
theorem endpointFirstSplit_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (front : List NodeId) (next : NodeId) (tail : List NodeId)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = front ++ next :: tail) (nonempty : front ≠ [])
    (readable : Ipv4Residents d nodes (front ++ [next]))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (fits : devicePrefixSpace d + (peerFixedSpace p + 4) + 28 * front.length ≤ NLMSG_GOODSIZE)
    (short : NLMSG_GOODSIZE < devicePrefixSpace d + (peerFixedSpace p + 4) + 28 * (front.length + 1)) :
    Returns (wgGetDeviceDump {hasWg := true} 0 {}) (fun g => g.dev = some d)
      (fun result g => result = endpointFirstCall d p nodes front next ∧ g.dev = some d) := by
  let skb : NlSkb := {room := NLMSG_GOODSIZE - devicePrefixSpace d}
  have allowed := (returns_iff _ _ _).mpr (dumpAllowed_front d nodes p front next tail listed nonempty readable
    {hasWg := true} skb {skb with room := skb.room - peerFixedSpace p}
    (hexKey p.remoteStatic) (peerFixedAttrs p) rfl
    (by dsimp [skb]; omega) (by dsimp [skb]; omega))
  have first := dumpTail_first_allowed d p {hasWg := true} skb _ rfl (by dsimp [skb]; omega) allowed
  have getter := multipart_getter_returns pid d p _ _ _ resident first
  have callback := deviceDump_single_contract pid d {hasWg := true}
    {hasWg := true,nextAllowedip := some next,allowedipsSeq := d.peerAllowedips.seq}
    0 (NLMSG_GOODSIZE - (devicePrefixSpace d + (peerFixedSpace p + 4) + 28 * front.length))
    (socketFirstPeer p nodes front) true peers rfl rfl (.inl rfl) header
    (by simpa [skb,socketFirstPeer,Nat.sub_sub,Nat.add_assoc] using getter)
  exact callback

/-- A nonempty fitting first page serializes its endpoint and entire IP list. -/
theorem endpointFirstComplete_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (first : NodeId) (rest : List NodeId)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = first :: rest) (readable : Ipv4Residents d nodes (first :: rest))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (fits : devicePrefixSpace d + (peerFixedSpace p + 4) + 28 * (first :: rest).length ≤ NLMSG_GOODSIZE) :
    Returns (wgGetDeviceDump {hasWg := true} 0 {}) (fun g => g.dev = some d)
      (fun result g => result = socketCallbackResult d {hasWg := true}
        (NLMSG_GOODSIZE - (devicePrefixSpace d + (peerFixedSpace p + 4) + 28 * (first :: rest).length))
        {socketFirstPeer p nodes (first :: rest) with split := false} false ∧ g.dev = some d) := by
  let skb : NlSkb := {room := NLMSG_GOODSIZE - devicePrefixSpace d}
  have allowed := (returns_iff _ _ _).mpr (dumpAllowed_suffix_all d nodes p
    {hasWg := true} skb {skb with room := skb.room - peerFixedSpace p}
    (hexKey p.remoteStatic) (peerFixedAttrs p) first (first :: rest) readable
    (by simp [listed]) (by simp) (.inl rfl)
    (by dsimp [skb]; simp only [List.length_cons] at fits ⊢; omega))
  have firstSource := dumpTail_first_allowed d p {hasWg := true} skb _ rfl
    (by dsimp [skb]; omega) (by simpa only [listed,List.head?_cons] using allowed)
  have getter := multipart_getter_returns pid d p _ _ _ resident firstSource
  exact deviceDump_single_contract pid d _ _ 0 _ _ false peers rfl rfl (.inl rfl) header
    (by simpa [skb,socketFirstPeer,Nat.sub_sub,Nat.add_assoc] using getter)
end Leanux.Proofs.WG.Config
