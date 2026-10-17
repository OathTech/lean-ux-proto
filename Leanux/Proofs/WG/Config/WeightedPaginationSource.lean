import Leanux.Proofs.WG.Config.WeightedPaginationModel
import Leanux.Proofs.WG.Config.MixedDumpScanSource
import Leanux.Proofs.WG.Config.SocketReadbackSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The original resumed fixed prefix feeds its actual remaining room and
public-key attribute to the allowed-IP continuation. -/
theorem dumpTail_resume_allowed_returns (d : Device) (p : Peer) (start : NodeId)
    (ctx : DumpCtx) (skb : NlSkb) (expected : PeerDumpResult)
    (cursor : ctx.nextAllowedip = some start) (room : 72 ≤ skb.room)
    (allowed : Returns (getPeerDumpAllowedSource p ctx skb {skb with room := skb.room - 40}
      (hexKey p.remoteStatic) [("public_key", toJson (hexKey p.remoteStatic))] (some start))
      (fun g => g.dev = some d) (fun result g => g.dev = some d ∧ result = expected)) :
    Returns (getPeerDumpTailSource p ctx skb) (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧ result = expected) := by
  intro g ambient device
  let mark (a : Ambient) (site : Decision) (value : Bool) :=
    {a with steps := a.steps.push {decision := site, outcome := value, netRx := a.netRxSection}}
  let before := mark (mark (mark ambient .getPeerNoNest false) .getPeerPubkeyFail false) .getPeerFirst false
  obtain ⟨result, final, after, run, finalDevice, value⟩ := allowed g before device
  refine ⟨result, final, after, ?_, finalDevice, value⟩
  rw [dumpTail_resume_source p start ctx skb cursor room]
  simpa [branch, AmbientM.branch, before, mark] using run

/-- The original resumed callback selects its true cursor suffix, then emits
the maximal fitting weighted prefix. Static residency and all-prior cursor
freshness discharge every read; no callback outcome is an input premise.
Repeated IDs away from the boundary and arbitrary stored widths remain allowed. -/
theorem mixedResumeCall_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (before : List NodeId) (start : NodeId) (rest : List NodeId)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = before ++ start :: rest) (fresh : start ∉ before)
    (readable : ∀ id ∈ start :: rest, d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE) :
    Returns (wgGetDeviceDump
      {hasWg := true, nextAllowedip := some start, allowedipsSeq := d.peerAllowedips.seq}
      d.deviceUpdateGen {}) (fun g => g.dev = some d)
      (fun result g => result = mixedResumeCall d p nodes start rest ∧ g.dev = some d) := by
  let ctx : DumpCtx := {hasWg := true, nextAllowedip := some start, allowedipsSeq := d.peerAllowedips.seq}
  let skb : NlSkb := {room := NLMSG_GOODSIZE - devicePrefixSpace d}
  have selected : p.allowedipsList.dropWhile (· != start) = start :: rest := by
    rw [listed, cursor_after_prefix before start rest fresh]
  have overhead (n : Nat) : 40 + (4 + n) = 44 + n := by omega
  have facts := weightedPrefix_spec nodes (NLMSG_GOODSIZE - devicePrefixSpace d - 44) (start :: rest)
  have progress := weightedPrefix_progress nodes (NLMSG_GOODSIZE - devicePrefixSpace d - 44)
    start rest (by have bound := (dumpNodeSpace_bounds (nodes start)).2; omega)
  cases plan : weightedPrefix nodes (NLMSG_GOODSIZE - devicePrefixSpace d - 44) (start :: rest) with
  | mk front remaining =>
    rw [plan] at facts progress
    dsimp only at facts progress
    have fits : devicePrefixSpace d + 44 + dumpNodesSpace nodes front ≤ NLMSG_GOODSIZE := by
      have h := facts.2.1
      omega
    cases remaining with
    | nil =>
      have decomp : front = start :: rest := by simpa using facts.1
      have reads : ∀ id ∈ front, d.nodes[id]? = some (nodes id) := by simpa only [decomp] using readable
      have allowed := dumpAllowed_weighted_all d nodes p ctx skb {skb with room := skb.room - 40}
        (hexKey p.remoteStatic) [("public_key", toJson (hexKey p.remoteStatic))] start front reads
        (by rw [decomp]; exact selected) progress.1 (.inr rfl) (by dsimp [skb]; omega)
      have tail := dumpTail_resume_allowed_returns d p start ctx skb _ rfl (by dsimp [skb]; omega) allowed
      have getter := multipart_getter_returns pid d p _ _ _ resident tail
      have call := deviceDump_single_contract pid d ctx {hasWg := true} d.deviceUpdateGen
        (NLMSG_GOODSIZE - (devicePrefixSpace d + 44 + dumpNodesSpace nodes front))
        {publicKey := hexKey p.remoteStatic,
         attrs := [("public_key", toJson (hexKey p.remoteStatic)), ("allowed_ips", Json.arr (dumpNodeJsons nodes front))]}
        false peers rfl rfl (.inr rfl) header
        (by simpa [ctx, skb, Nat.sub_sub, Nat.add_assoc, overhead] using getter)
      simpa [mixedResumeCall, plan, ctx] using call
    | cons next tailIds =>
      have decomp : front ++ next :: tailIds = start :: rest := facts.1
      have reads : ∀ id ∈ front ++ [next], d.nodes[id]? = some (nodes id) := by
        intro id member
        apply readable id
        rw [← decomp]
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
        rcases member with member | same
        · exact .inl member
        · exact .inr (.inl same)
      have short := facts.2.2 next tailIds rfl
      have allowed := dumpAllowed_weighted_split d nodes p ctx skb {skb with room := skb.room - 40}
        (hexKey p.remoteStatic) [("public_key", toJson (hexKey p.remoteStatic))]
        start front next tailIds reads (by rw [decomp]; exact selected) (.inr rfl)
        (by dsimp [skb]; omega) (by dsimp [skb]; omega)
      have tail := dumpTail_resume_allowed_returns d p start ctx skb _ rfl (by dsimp [skb]; omega) allowed
      have getter := multipart_getter_returns pid d p _ _ _ resident tail
      have call := deviceDump_single_contract pid d ctx
        {hasWg := true, nextAllowedip := some next, allowedipsSeq := d.peerAllowedips.seq}
        d.deviceUpdateGen (NLMSG_GOODSIZE - (devicePrefixSpace d + 44 + dumpNodesSpace nodes front))
        {publicKey := hexKey p.remoteStatic,
         attrs := [("public_key", toJson (hexKey p.remoteStatic)), ("allowed_ips", Json.arr (dumpNodeJsons nodes front))], split := true}
        true peers rfl rfl (.inr rfl) header
        (by simpa [ctx, skb, Nat.sub_sub, Nat.add_assoc, overhead] using getter)
      simpa [mixedResumeCall, plan, ctx] using call

end Leanux.Proofs.WG.Config
