import Leanux.Proofs.WG.Config.SuffixReadbackModel
import Leanux.Proofs.WG.Config.MultipartClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- The original allowed-IP loop and its completion, with the accumulated IPs
explicit for induction. All original node reads, guards and split exits remain. -/
def suffixScan (ctx : DumpCtx) (pubkey : String) (attrs : List (String × Json))
    (ids : List NodeId) (skb : NlSkb) (ips : Array Json) : M PeerDumpResult := do
  let mut skb := skb
  let mut ips := ips
  for id in ids do
    _ ← branch .getPeerAipIter true
    let (family, masked, cidr) ← readNode (← getNode id)
    let (s, ip) ← getAllowedips skb family masked cidr
    skb := s
    if ← branch .getPeerAipFail ip.isNone then
      return (skb, { ctx with nextAllowedip := some id },
        .split { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr ips)], split := true })
    ips := ips.push ip.get!
  _ ← branch .getPeerAipIter false
  return (skb, { ctx with nextAllowedip := none, allowedipsSeq := 0 },
    .complete { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr ips)] })

theorem suffixScan_nil (ctx : DumpCtx) (pubkey : String) (attrs : List (String × Json))
    (skb : NlSkb) (ips : Array Json) :
    suffixScan ctx pubkey attrs [] skb ips = (do
      _ ← branch .getPeerAipIter false
      pure (skb, { ctx with nextAllowedip := none, allowedipsSeq := 0 },
        .complete { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr ips)] })) := by
  simp [suffixScan, List.forIn_nil]

theorem suffixScan_cons (ctx : DumpCtx) (pubkey : String) (attrs : List (String × Json))
    (id : NodeId) (ids : List NodeId) (skb : NlSkb) (ips : Array Json) :
    suffixScan ctx pubkey attrs (id :: ids) skb ips = (do
      _ ← branch .getPeerAipIter true
      let (family, masked, cidr) ← readNode (← getNode id)
      let (s, ip) ← getAllowedips skb family masked cidr
      if ← branch .getPeerAipFail ip.isNone then
        pure (s, { ctx with nextAllowedip := some id },
          .split { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr ips)], split := true })
      else suffixScan ctx pubkey attrs ids s (ips.push ip.get!)) := by
  simp [suffixScan, List.forIn_cons, bind_assoc]
  congr 1
  funext ignored
  congr 1
  funext n
  congr 1
  funext read
  congr 1
  funext got
  congr 1
  funext failed
  cases failed <;> simp

/-- Exact factoring, including cancellation, sequence-change completion and
the original stale-cursor failure, before any residency or room assumptions. -/
theorem dumpAllowed_suffix_source (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json)) (node : Option NodeId) :
    getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs node = (do
      let mut ctx := ctx
      if ← branch .getPeerNoAips node.isNone then
        return (skb, { ctx with nextAllowedip := none, allowedipsSeq := 0 },
          .complete { publicKey := pubkey, attrs })
      let seq := (← getDev).peerAllowedips.seq
      if ← branch .getPeerSeqUnset (ctx.allowedipsSeq == 0) then
        ctx := { ctx with allowedipsSeq := seq }
      else if ← branch .getPeerSeqChanged (ctx.allowedipsSeq != seq) then
        return (skb, { ctx with nextAllowedip := none, allowedipsSeq := 0 },
          .complete { publicKey := pubkey, attrs })
      let (fail, s) := skb.put (nlaTotal 0)
      if ← branch .getPeerAipsNestFail fail then return (skb0, ctx, .cancelled)
      let some start := node | invariant "unreachable"
      let rest := p.allowedipsList.dropWhile (· != start)
      if rest.isEmpty then invariant "a stale allowed-IPs cursor with an unchanged sequence (2.4)"
      suffixScan ctx pubkey attrs rest s #[]) := by
  rfl

theorem readNode_ipv4 (n : AipNode) (width : n.bitlen = 32) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ readNode n
    ⦃⇓ result w => ⌜P w.k ∧ result = (4, allowedMasked true n.bits n.cidr, n.cidr)⌝⦄ := by
  mvcgen [readNode, swapEndian, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [width, allowedMasked, allowedBits]
  all_goals grind only

/-- An arbitrary finite resident IPv4 suffix fits and is serialized in order.
Repeated IDs are allowed: this theorem scans once, without a cursor restart. -/
theorem suffixScan_all (d : Device) (nodes : NodeId → AipNode) (ids : List NodeId)
    (resident : Ipv4Residents d nodes ids) (ctx : DumpCtx) (pubkey : String)
    (attrs : List (String × Json)) (skb : NlSkb) (ips : Array Json)
    (room : 28 * ids.length ≤ skb.room) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ suffixScan ctx pubkey attrs ids skb ips
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
      ({ skb with room := skb.room - 28 * ids.length },
       { ctx with nextAllowedip := none, allowedipsSeq := 0 },
       .complete { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr (ips ++ ipv4Jsons nodes ids))] })⌝⦄ := by
  induction ids generalizing skb ips with
  | nil =>
    rw [suffixScan_nil]
    mvcgen [branch]
    all_goals simp_all [ipv4Jsons]
  | cons id ids ih =>
    have here := resident id (by simp)
    have tail : Ipv4Residents d nodes ids := fun n hn => resident n (by simp [hn])
    have hg := multipart_getNode id d (nodes id) here.1
    have hn := readNode_ipv4 (nodes id) here.2 (fun k => k.wg = some d)
    have ha := getAllowedips_inserted true (nodes id).bits (nodes id).cidr skb
      (by change 28 ≤ skb.room; simp only [List.length_cons] at room; omega)
      (fun k => k.wg = some d)
    have ht := ih tail { skb with room := skb.room - 28 }
      (ips.push (ipv4NodeJson (nodes id)))
      (by simp only [List.length_cons] at room; dsimp; omega)
    rw [suffixScan_cons]
    mvcgen [branch, hg, hn, ha, ht]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [allowedFamily, allowedIpSpace, nlaTotal, ipv4NodeJson]
    all_goals subst_vars
    all_goals mvcgen [hn, ha, ht, branch]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [allowedFamily, allowedIpSpace, nlaTotal, ipv4NodeJson,
      ipv4Jsons, List.length_cons, Nat.mul_add, Nat.sub_sub, Array.push_append, Array.append_assoc]
    all_goals subst_vars
    all_goals mvcgen [hn, ha, ht, branch]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [allowedFamily, allowedIpSpace, nlaTotal, ipv4NodeJson,
      ipv4Jsons, List.length_cons, Nat.mul_add, Nat.sub_sub, Nat.add_comm]
    all_goals subst_vars
    all_goals mvcgen [ht, branch]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [allowedFamily, allowedIpSpace, nlaTotal, ipv4NodeJson,
      ipv4Jsons, List.length_cons, Nat.mul_add, Nat.sub_sub, Nat.add_comm]

/-- The unchanged original header selects this nonempty suffix and reserves
its outer nest. The supplied scan contract is over its actual initialized seq. -/
theorem dumpAllowed_scan (d : Device) (p : Peer) (ctx : DumpCtx)
    (skb0 skb : NlSkb) (pubkey : String) (attrs : List (String × Json))
    (start : NodeId) (ids : List NodeId) (expected : PeerDumpResult)
    (selected : p.allowedipsList.dropWhile (· != start) = ids) (nonempty : ids ≠ [])
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 4 ≤ skb.room)
    (scan : ⦃fun w => ⌜w.k.wg = some d⌝⦄
      suffixScan { ctx with allowedipsSeq := d.peerAllowedips.seq } pubkey attrs ids
        { skb with room := skb.room - 4 } #[]
      ⦃⇓ result w => ⌜w.k.wg = some d ∧ result = expected⌝⦄) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄
      getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs (some start)
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result = expected⌝⦄ := by
  rcases sequence with sequence | sequence
  all_goals rw [dumpAllowed_suffix_source]
  all_goals simp [selected, nonempty, NlSkb.put, nlaTotal, show ¬ skb.room < 4 by omega]
  all_goals mvcgen [branch, getDev, getK, invariant, scan]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all
  all_goals subst_vars
  all_goals mvcgen [branch, scan]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all
  all_goals mvcgen [branch, scan]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all

  all_goals cases ctx
  all_goals simp_all
  all_goals mvcgen [scan]
  all_goals assumption

/-- The first IPv4 node fits; reading the second then discovers no remaining
space. Later nodes are neither read nor required resident by this contract. -/
theorem suffixScan_split_one (d : Device) (nodes : NodeId → AipNode)
    (a b : NodeId) (tail : List NodeId) (ctx : DumpCtx) (pubkey : String)
    (attrs : List (String × Json)) (skb : NlSkb)
    (resident : Ipv4Residents d nodes [a, b]) (room : skb.room = 28) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ suffixScan ctx pubkey attrs (a :: b :: tail) skb #[]
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
      ({ skb with room := 0 }, { ctx with nextAllowedip := some b },
        .split { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr #[ipv4NodeJson (nodes a)])], split := true })⌝⦄ := by
  have ra := resident a (by simp)
  have rb := resident b (by simp)
  have ga := multipart_getNode a d (nodes a) ra.1
  have gb := multipart_getNode b d (nodes b) rb.1
  have na := readNode_ipv4 (nodes a) ra.2 (fun k => k.wg = some d)
  have nb := readNode_ipv4 (nodes b) rb.2 (fun k => k.wg = some d)
  have ha := getAllowedips_inserted true (nodes a).bits (nodes a).cidr skb
    (by change 28 ≤ skb.room; omega) (fun k => k.wg = some d)
  have hz := getAllowedips_zero { skb with room := 0 } 4
    (allowedMasked true (nodes b).bits (nodes b).cidr) (nodes b).cidr rfl
    (fun k => k.wg = some d)
  rw [suffixScan_cons]
  simp only [suffixScan_cons]
  mvcgen [branch, ga, gb, na, nb, ha, hz]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [room, allowedFamily, allowedIpSpace, nlaTotal, ipv4NodeJson]
  all_goals subst_vars
  all_goals mvcgen [branch, ga, gb, na, nb, ha, hz]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [room, allowedFamily, allowedIpSpace, nlaTotal, ipv4NodeJson]
  all_goals subst_vars
  all_goals mvcgen [branch, ga, gb, na, nb, ha, hz]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [room, allowedFamily, allowedIpSpace, nlaTotal, ipv4NodeJson]
  all_goals subst_vars
  all_goals mvcgen [branch, ga, gb, na, nb, ha, hz]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [room, allowedFamily, allowedIpSpace, nlaTotal, ipv4NodeJson]
  all_goals subst_vars
  all_goals mvcgen [branch, ga, gb, na, nb, ha, hz]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [room, allowedFamily, allowedIpSpace, nlaTotal, ipv4NodeJson]
  all_goals subst_vars
  all_goals mvcgen [branch, ga, gb, na, nb, ha, hz]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [room, allowedFamily, allowedIpSpace, nlaTotal, ipv4NodeJson]

theorem dumpAllowed_suffix_all (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json)) (start : NodeId) (ids : List NodeId)
    (resident : Ipv4Residents d nodes ids)
    (selected : p.allowedipsList.dropWhile (· != start) = ids) (nonempty : ids ≠ [])
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 4 + 28 * ids.length ≤ skb.room) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs (some start)
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
      ({ skb with room := skb.room - (4 + 28 * ids.length) },
       { ctx with nextAllowedip := none, allowedipsSeq := 0 },
       .complete { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr (ipv4Jsons nodes ids))] })⌝⦄ := by
  apply dumpAllowed_scan d p ctx skb0 skb pubkey attrs start ids _ selected nonempty sequence (by omega)
  simpa [Nat.sub_sub] using suffixScan_all d nodes ids resident
    { ctx with allowedipsSeq := d.peerAllowedips.seq } pubkey attrs
    { skb with room := skb.room - 4 } #[] (by dsimp; omega)

theorem dumpAllowed_suffix_split (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (a b : NodeId) (tail : List NodeId) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json))
    (listed : p.allowedipsList = a :: b :: tail) (resident : Ipv4Residents d nodes [a, b])
    (sequence : ctx.allowedipsSeq = 0) (room : skb.room = 32) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs (some a)
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
      ({ skb with room := 0 }, { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq },
       .split { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr #[ipv4NodeJson (nodes a)])], split := true })⌝⦄ := by
  apply dumpAllowed_scan d p ctx skb0 skb pubkey attrs a (a :: b :: tail) _
    (by simp [listed]) (by simp) (.inl sequence) (by omega)
  simpa using suffixScan_split_one d nodes a b tail
    { ctx with allowedipsSeq := d.peerAllowedips.seq } pubkey attrs
    { skb with room := skb.room - 4 } resident (by dsimp; omega)

theorem dumpTail_suffix_split (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (a b : NodeId) (tail : List NodeId) (ctx : DumpCtx) (skb : NlSkb)
    (listed : p.allowedipsList = a :: b :: tail) (endpoint : p.endpoint = none)
    (resident : Ipv4Residents d nodes [a, b])
    (fresh : ctx.nextAllowedip = none) (sequence : ctx.allowedipsSeq = 0) (room : skb.room = 168) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
      ({ skb with room := 0 }, { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq },
       .split (multipartFirst p (nodes a).bits (nodes a).cidr))⌝⦄ := by
  have ha := dumpAllowed_suffix_split d nodes p a b tail ctx skb
    { skb with room := 32 } (hexKey p.remoteStatic) (peerFixedAttrs p)
    listed resident sequence rfl
  simp only [getPeerDumpTailSource, fresh]
  simp [NlSkb.put, nlaTotal, room, endpoint, AF_INET, AF_INET6, listed]
  mvcgen [branch, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerFixedAttrs, endpoint, multipartFirst, ipv4NodeJson]
  all_goals subst_vars
  all_goals mvcgen [ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [peerFixedAttrs, endpoint, multipartFirst, ipv4NodeJson]

theorem dumpTail_suffix_resume (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (a b : NodeId) (tail : List NodeId) (ctx : DumpCtx) (skb : NlSkb)
    (listed : p.allowedipsList = a :: b :: tail) (distinct : a ≠ b)
    (resident : Ipv4Residents d nodes (b :: tail))
    (cursor : ctx.nextAllowedip = some b) (sequence : ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 44 + 28 * (1 + tail.length) ≤ skb.room) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
      ({ skb with room := skb.room - (44 + 28 * (1 + tail.length)) },
       { ctx with nextAllowedip := none, allowedipsSeq := 0 },
       .complete (suffixLast p nodes (b :: tail)))⌝⦄ := by
  have ha := dumpAllowed_suffix_all d nodes p ctx skb
    { skb with room := skb.room - 40 } (hexKey p.remoteStatic)
    [("public_key", toJson (hexKey p.remoteStatic))] b (b :: tail) resident
    (by simp [listed, distinct]) (by simp) (.inr sequence)
    (by simp only [List.length_cons]; omega)
  rw [dumpTail_resume_source p b ctx skb cursor (by omega)]
  mvcgen [branch, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [suffixLast, Nat.sub_sub, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  all_goals omega

end Leanux.Proofs.WG.Config
