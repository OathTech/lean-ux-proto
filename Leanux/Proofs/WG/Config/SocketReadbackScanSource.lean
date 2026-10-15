import Leanux.Proofs.WG.Config.SocketReadbackModel

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- A short IPv4 IP nest rolls back every successful partial put. The original
guard sequence is retained, including nonzero residual room. -/
theorem getAllowedips_ipv4_short (skb : NlSkb) (masked cidr : Nat)
    (room : skb.room < 28) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ getAllowedips skb 4 masked cidr
    ⦃⇓ result w => ⌜P w.k ∧ result = (skb, none)⌝⦄ := by
  mvcgen [getAllowedips, NlSkb.put, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [nlaTotal]
  all_goals split at * <;> simp_all
  all_goals try (split at * <;> simp_all)
  all_goals try (split at * <;> simp_all)
  all_goals try (split at * <;> simp_all)
  all_goals omega

/-- The scan consumes a fitting front, reads the next resident node, and
splits there. No residency premise is needed for the uninspected tail. -/
theorem suffixScan_prefix_split (d : Device) (nodes : NodeId → AipNode)
    (front : List NodeId) (b : NodeId) (tail : List NodeId)
    (resident : Ipv4Residents d nodes (front ++ [b]))
    (ctx : DumpCtx) (pubkey : String) (attrs : List (String × Json))
    (skb : NlSkb) (ips : Array Json)
    (fits : 28 * front.length ≤ skb.room)
    (short : skb.room < 28 * (front.length + 1)) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ suffixScan ctx pubkey attrs (front ++ b :: tail) skb ips
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
      ({ skb with room := skb.room - 28 * front.length }, { ctx with nextAllowedip := some b },
       .split { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr (ips ++ ipv4Jsons nodes front))], split := true })⌝⦄ := by
  induction front generalizing skb ips with
  | nil =>
    have rb := resident b (by simp)
    have hg := multipart_getNode b d (nodes b) rb.1
    have hn := readNode_ipv4 (nodes b) rb.2 (fun k => k.wg = some d)
    have ha := getAllowedips_ipv4_short skb (allowedMasked true (nodes b).bits (nodes b).cidr)
      (nodes b).cidr (by simpa using short) (fun k => k.wg = some d)
    simp only [List.nil_append, suffixScan_cons]
    mvcgen [branch, hg, hn, ha]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [ipv4Jsons]
    all_goals subst_vars
    all_goals mvcgen [branch, hn, ha]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [ipv4Jsons]
    all_goals subst_vars
    all_goals mvcgen [branch, ha]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [ipv4Jsons]
  | cons a front ih =>
    have ra := resident a (by simp)
    have others : Ipv4Residents d nodes (front ++ [b]) := by
      intro id member
      exact resident id (by simp [member])
    have hg := multipart_getNode a d (nodes a) ra.1
    have hn := readNode_ipv4 (nodes a) ra.2 (fun k => k.wg = some d)
    have ha := getAllowedips_inserted true (nodes a).bits (nodes a).cidr skb
      (by change 28 ≤ skb.room; simp only [List.length_cons] at fits; omega)
      (fun k => k.wg = some d)
    have ht := ih others { skb with room := skb.room - 28 } (ips.push (ipv4NodeJson (nodes a)))
      (by simp only [List.length_cons] at fits; dsimp; omega)
      (by simp only [List.length_cons] at short fits; dsimp; omega)
    simp only [List.cons_append, suffixScan_cons]
    mvcgen [branch, hg, hn, ha, ht]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [allowedFamily, allowedIpSpace, nlaTotal, ipv4NodeJson]
    all_goals subst_vars
    all_goals mvcgen [branch, hn, ha, ht]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [allowedFamily, allowedIpSpace, nlaTotal, ipv4NodeJson]
    all_goals subst_vars
    all_goals mvcgen [branch, ha, ht]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [allowedFamily, allowedIpSpace, nlaTotal, ipv4NodeJson,
      ipv4Jsons, List.length_cons, Nat.mul_add, Nat.sub_sub, Nat.add_comm]
    all_goals subst_vars
    all_goals mvcgen [branch, ht]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all [ipv4NodeJson, ipv4Jsons, List.length_cons,
      Nat.mul_add, Nat.sub_sub, Nat.add_comm]

theorem cursor_after_prefix (front : List NodeId) (b : NodeId) (tail : List NodeId)
    (absent : b ∉ front) :
    (front ++ b :: tail).dropWhile (· != b) = b :: tail := by
  induction front with
  | nil => simp
  | cons a front ih => simp_all [ne_comm]

theorem dumpAllowed_front (d : Device) (nodes : NodeId → AipNode) (p : Peer)
    (front : List NodeId) (b : NodeId) (tail : List NodeId)
    (listed : p.allowedipsList = front ++ b :: tail) (nonempty : front ≠ [])
    (resident : Ipv4Residents d nodes (front ++ [b]))
    (ctx : DumpCtx) (skb0 skb : NlSkb) (pubkey : String) (attrs : List (String × Json))
    (sequence : ctx.allowedipsSeq = 0)
    (fits : 4 + 28 * front.length ≤ skb.room)
    (short : skb.room < 4 + 28 * (front.length + 1)) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄
      getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs p.allowedipsList.head?
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
      ({ skb with room := skb.room - (4 + 28 * front.length) },
       { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq },
       .split { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr (ipv4Jsons nodes front))], split := true })⌝⦄ := by
  cases front with
  | nil => contradiction
  | cons a front =>
    simp only [List.length_cons] at fits short
    simp only [listed, List.cons_append, List.head?_cons]
    apply dumpAllowed_scan d p ctx skb0 skb pubkey attrs a ((a :: front) ++ b :: tail) _
      (by simp [listed]) (by simp) (.inl sequence) (by omega)
    simpa [Nat.sub_sub] using suffixScan_prefix_split d nodes (a :: front) b tail resident
      { ctx with allowedipsSeq := d.peerAllowedips.seq } pubkey attrs
      { skb with room := skb.room - 4 } #[] (by dsimp; omega) (by dsimp; omega)

theorem dumpTail_front (d : Device) (nodes : NodeId → AipNode) (p : Peer)
    (front : List NodeId) (b : NodeId) (tail : List NodeId)
    (listed : p.allowedipsList = front ++ b :: tail) (nonempty : front ≠ [])
    (resident : Ipv4Residents d nodes (front ++ [b])) (endpoint : p.endpoint = none)
    (ctx : DumpCtx) (skb : NlSkb) (fresh : ctx.nextAllowedip = none)
    (sequence : ctx.allowedipsSeq = 0)
    (fits : 140 + 28 * front.length ≤ skb.room)
    (short : skb.room < 140 + 28 * (front.length + 1)) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
      ({ skb with room := skb.room - (140 + 28 * front.length) },
       { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq },
       .split (socketFirstPeer p nodes front))⌝⦄ := by
  have ha := dumpAllowed_front d nodes p front b tail listed nonempty resident ctx skb
    { skb with room := skb.room - 136 } (hexKey p.remoteStatic) (peerFixedAttrs p) sequence
    (by dsimp; omega) (by dsimp; omega)
  have r4 : ¬ skb.room < 4 := by omega
  have r40 : ¬ skb.room - 4 < 36 := by omega
  have r76 : ¬ skb.room - 40 < 36 := by omega
  have r96 : ¬ skb.room - 76 < 20 := by omega
  have r104 : ¬ skb.room - 96 < 8 := by omega
  have r116 : ¬ skb.room - 104 < 12 := by omega
  have r128 : ¬ skb.room - 116 < 12 := by omega
  have r136 : ¬ skb.room - 128 < 8 := by omega
  simp only [getPeerDumpTailSource, fresh]
  simp [NlSkb.put, nlaTotal, Nat.sub_sub, endpoint, AF_INET, AF_INET6,
    r4, r40, r76, r96, r104, r116, r128, r136]
  mvcgen [branch, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerFixedAttrs, endpoint, socketFirstPeer, Nat.sub_sub]
  all_goals subst_vars
  all_goals mvcgen [ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerFixedAttrs, endpoint, socketFirstPeer, Nat.sub_sub]
  all_goals omega

theorem dumpTail_after_front (d : Device) (nodes : NodeId → AipNode) (p : Peer)
    (front : List NodeId) (b : NodeId) (tail : List NodeId)
    (listed : p.allowedipsList = front ++ b :: tail) (absent : b ∉ front)
    (resident : Ipv4Residents d nodes (b :: tail)) (ctx : DumpCtx) (skb : NlSkb)
    (cursor : ctx.nextAllowedip = some b) (sequence : ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 44 + 28 * (b :: tail).length ≤ skb.room) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
      ({ skb with room := skb.room - (44 + 28 * (b :: tail).length) },
       { ctx with nextAllowedip := none, allowedipsSeq := 0 },
       .complete (suffixLast p nodes (b :: tail)))⌝⦄ := by
  have ha := dumpAllowed_suffix_all d nodes p ctx skb
    { skb with room := skb.room - 40 } (hexKey p.remoteStatic)
    [("public_key", toJson (hexKey p.remoteStatic))] b (b :: tail) resident
    (by rw [listed]; exact cursor_after_prefix front b tail absent) (by simp) (.inr sequence)
    (by simp only [List.length_cons] at room ⊢; omega)
  rw [dumpTail_resume_source p b ctx skb cursor (by simp only [List.length_cons] at room; omega)]
  mvcgen [branch, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [suffixLast, Nat.sub_sub]
  all_goals omega

end Leanux.Proofs.WG.Config
