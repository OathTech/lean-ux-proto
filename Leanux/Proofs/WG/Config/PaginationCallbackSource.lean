import Leanux.Proofs.WG.Config.SocketReadbackSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- A genuine resumed peer dump can split again. The selected suffix is the
actual first-occurrence cursor lookup, rather than a supplied execution. -/
theorem dumpTail_resume_split (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (start : NodeId) (front : List NodeId) (next : NodeId)
    (tail : List NodeId) (ctx : DumpCtx) (skb : NlSkb)
    (selected : p.allowedipsList.dropWhile (· != start) = front ++ next :: tail)
    (nonempty : front ≠ []) (readable : Ipv4Residents d nodes (front ++ [next]))
    (cursor : ctx.nextAllowedip = some start)
    (sequence : ctx.allowedipsSeq = d.peerAllowedips.seq)
    (fits : 44 + 28 * front.length ≤ skb.room)
    (short : skb.room < 44 + 28 * (front.length + 1)) :
    Returns (getPeerDumpTailSource p ctx skb) (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧ result =
        ({skb with room := skb.room - (44 + 28 * front.length)},
         {ctx with nextAllowedip := some next, allowedipsSeq := d.peerAllowedips.seq},
         .split {suffixLast p nodes front with split := true})) := by
  have positive : 0 < front.length := List.length_pos_iff.mpr nonempty
  have scan := suffixScan_prefix_split d nodes front next tail readable
    {ctx with allowedipsSeq := d.peerAllowedips.seq} (hexKey p.remoteStatic)
    [("public_key",toJson (hexKey p.remoteStatic))]
    {skb with room := skb.room - 40 - 4} #[]
    (by dsimp; omega) (by dsimp; omega)
  have allowed := dumpAllowed_scan d p ctx skb {skb with room := skb.room - 40}
    (hexKey p.remoteStatic) [("public_key",toJson (hexKey p.remoteStatic))]
    start (front ++ next :: tail) _ selected (by simp) (.inr sequence)
    (by dsimp; omega) scan
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision,outcome,netRx := a.netRxSection}}
  let before := mark (mark (mark ambient .getPeerNoNest false)
    .getPeerPubkeyFail false) .getPeerFirst false
  obtain ⟨result,final,after,run,finalDevice,value⟩ :=
    (returns_iff _ _ _).mpr allowed g before device
  refine ⟨result,final,after,?_,finalDevice,?_⟩
  · rw [dumpTail_resume_source p start ctx skb cursor (by omega)]
    simpa [branch,AmbientM.branch,before,mark] using run
  · simpa [suffixLast,ipv4Jsons,Nat.sub_sub,Nat.add_assoc] using value

/-- The actual fixed-capacity callback repeats a resumed peer's partial DATA
and sets the allowed-IP cursor to the next un-emitted node. Its peer cursor
remains NULL; repeated node IDs need not advance its first-occurrence lookup. -/
theorem socketResumeCall_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (start : NodeId) (front : List NodeId)
    (next : NodeId) (tail : List NodeId)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (selected : p.allowedipsList.dropWhile (· != start) = front ++ next :: tail)
    (nonempty : front ≠ []) (readable : Ipv4Residents d nodes (front ++ [next]))
    (headerFits : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (fits : devicePrefixSpace d + 44 + 28 * front.length ≤ NLMSG_GOODSIZE)
    (short : NLMSG_GOODSIZE < devicePrefixSpace d + 44 + 28 * (front.length + 1)) :
    Returns (wgGetDeviceDump
      {hasWg := true,nextAllowedip := some start,allowedipsSeq := d.peerAllowedips.seq}
      d.deviceUpdateGen {}) (fun g => g.dev = some d)
      (fun result g => result = socketCallbackResult d
        {hasWg := true,nextAllowedip := some next,allowedipsSeq := d.peerAllowedips.seq}
        (NLMSG_GOODSIZE - devicePrefixSpace d - (44 + 28 * front.length))
        {suffixLast p nodes front with split := true} true ∧ g.dev = some d) := by
  have tail := dumpTail_resume_split d nodes p start front next tail
    {hasWg := true,nextAllowedip := some start,allowedipsSeq := d.peerAllowedips.seq}
    {room := NLMSG_GOODSIZE - devicePrefixSpace d} selected nonempty readable rfl rfl
    (by dsimp; omega) (by dsimp; omega)
  have getter := multipart_getter_returns pid d p _ _ _ resident tail
  exact deviceDump_single_contract pid d _ _ d.deviceUpdateGen _ _ true peers
    rfl rfl (.inr rfl) headerFits getter

end Leanux.Proofs.WG.Config
