import Leanux.Proofs.WG.Config.SocketReadbackFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem cursor_after_prefix (front : List NodeId) (b : NodeId) (tail : List NodeId)
    (absent : b ∉ front) :
    (front ++ b :: tail).dropWhile (· != b) = b :: tail := by
  induction front with
  | nil => simp
  | cons a front ih => simp_all [ne_comm]

theorem suffixScan_prefix_split (d : Device) (nodes : NodeId → AipNode)
    (front : List NodeId) (b : NodeId) (tail : List NodeId)
    (resident : Ipv4Residents d nodes (front ++ [b]))
    (ctx : DumpCtx) (pubkey : String) (attrs : List (String × Json))
    (skb : NlSkb) (ips : Array Json)
    (fits : 28 * front.length ≤ skb.room)
    (short : skb.room < 28 * (front.length + 1)) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ suffixScan ctx pubkey attrs (front ++ b :: tail) skb ips
    ⦃⇓ result w => ⌜w.dev = some d ∧ result =
      ({ skb with room := skb.room - 28 * front.length }, { ctx with nextAllowedip := some b },
       .split { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr (ips ++ ipv4Jsons nodes front))], split := true })⌝⦄ := by
  induction front generalizing skb ips with
  | nil =>
    have rb := resident b (by simp)
    apply (returns_iff _ _ _).mp
    intro g ambient device
    let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
      {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
    let before := mark ambient .getPeerAipIter true
    obtain ⟨n, g1, a1, getRun, dev1, value1⟩ :=
      (returns_iff _ _ _).mpr (multipart_getNode b d _ rb.1) g before device
    subst n
    obtain ⟨r, g2, a2, readRun, dev2, value2⟩ :=
      (returns_iff _ _ _).mpr (readNode_ipv4_native (nodes b) rb.2
        (fun g => g.dev = some d)) g1 a1 dev1
    subst r
    obtain ⟨serialized, final, a3, serializeRun, finalDevice, value3⟩ :=
      (returns_iff _ _ _).mpr (getAllowedips_ipv4_short_native skb
        (allowedMasked true (nodes b).bits (nodes b).cidr) (nodes b).cidr
        (by simpa using short) (fun g => g.dev = some d)) g2 a2 dev2
    subst serialized
    let after := mark a3 .getPeerAipFail true
    refine ⟨_, final, after, ?_, finalDevice, rfl⟩
    have getLift (nid : NodeId) : (monadLift (getNode nid) : WG.M AipNode) =
        liftAip (getNode nid) := rfl
    simp only [List.nil_append, suffixScan_cons, getLift]
    simp [branch, AmbientM.branch, before, after, mark, ipv4Jsons] at getRun ⊢
    rw [getRun]
    dsimp only [bind, Except.bind]
    rw [readRun]
    dsimp only [bind, Except.bind]
    rw [serializeRun]
    rfl
  | cons id front ih =>
    have here := resident id (by simp)
    have others : Ipv4Residents d nodes (front ++ [b]) := fun n hn => resident n (by simp [hn])
    apply (returns_iff _ _ _).mp
    intro g ambient device
    let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
      {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
    let before := mark ambient .getPeerAipIter true
    obtain ⟨n, g1, a1, getRun, dev1, value1⟩ :=
      (returns_iff _ _ _).mpr (multipart_getNode id d _ here.1) g before device
    subst n
    obtain ⟨r, g2, a2, readRun, dev2, value2⟩ :=
      (returns_iff _ _ _).mpr (readNode_ipv4_native (nodes id) here.2
        (fun g => g.dev = some d)) g1 a1 dev1
    subst r
    obtain ⟨serialized, g3, a3, serializeRun, dev3, value3⟩ :=
      (returns_iff _ _ _).mpr (getAllowedips_inserted true (nodes id).bits (nodes id).cidr skb
        (by change 28 ≤ skb.room; simp only [List.length_cons] at fits; omega)
        (fun g => g.dev = some d)) g2 a2 dev2
    subst serialized
    let next := mark a3 .getPeerAipFail false
    obtain ⟨result, final, after, tailRun, finalDevice, value⟩ :=
      (returns_iff _ _ _).mpr (ih others {skb with room := skb.room - 28}
        (ips.push (ipv4NodeJson (nodes id)))
        (by simp only [List.length_cons] at fits; dsimp; omega)
        (by simp only [List.length_cons] at fits short; dsimp; omega)) g3 next dev3
    refine ⟨result, final, after, ?_, finalDevice, ?_⟩
    · have getLift (nid : NodeId) : (monadLift (getNode nid) : WG.M AipNode) =
          liftAip (getNode nid) := rfl
      simp only [List.cons_append, suffixScan_cons, getLift]
      simp [branch, AmbientM.branch, before, next, mark, allowedFamily, allowedIpSpace,
        nlaTotal] at getRun readRun serializeRun tailRun ⊢
      rw [getRun]
      dsimp only [bind, Except.bind]
      rw [readRun]
      dsimp only [bind, Except.bind]
      rw [serializeRun]
      simpa [branch, AmbientM.branch, ipv4NodeJson] using tailRun
    · simpa [ipv4Jsons, List.length_cons, Nat.mul_add, Nat.sub_sub, Array.push_append,
        Array.append_assoc, Nat.add_comm] using value

theorem dumpAllowed_front (d : Device) (nodes : NodeId → AipNode) (p : Peer)
    (front : List NodeId) (b : NodeId) (tail : List NodeId)
    (listed : p.allowedipsList = front ++ b :: tail) (nonempty : front ≠ [])
    (resident : Ipv4Residents d nodes (front ++ [b]))
    (ctx : DumpCtx) (skb0 skb : NlSkb) (pubkey : String) (attrs : List (String × Json))
    (sequence : ctx.allowedipsSeq = 0)
    (fits : 4 + 28 * front.length ≤ skb.room)
    (short : skb.room < 4 + 28 * (front.length + 1)) :
    ⦃fun w => ⌜w.dev = some d⌝⦄
      getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs p.allowedipsList.head?
    ⦃⇓ result w => ⌜w.dev = some d ∧ result =
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
    ⦃fun w => ⌜w.dev = some d⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓ result w => ⌜w.dev = some d ∧ result =
      ({ skb with room := skb.room - (140 + 28 * front.length) },
       { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq },
       .split (socketFirstPeer p nodes front))⌝⦄ := by
  have r4 : ¬ skb.room < 4 := by omega
  have r40 : ¬ skb.room - 4 < 36 := by omega
  have r76 : ¬ skb.room - 40 < 36 := by omega
  have r96 : ¬ skb.room - 76 < 20 := by omega
  have r104 : ¬ skb.room - 96 < 8 := by omega
  have r116 : ¬ skb.room - 104 < 12 := by omega
  have r128 : ¬ skb.room - 116 < 12 := by omega
  have r136 : ¬ skb.room - 128 < 8 := by omega
  apply (returns_iff _ _ _).mp
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let before := mark (mark (mark (mark (mark (mark (mark (mark (mark (mark
    (mark (mark ambient .getPeerNoNest false) .getPeerPubkeyFail false) .getPeerFirst true)
    .getPeerPskFail false) .getPeerPutHandshake false) .getPeerPutKeepalive false)
    .getPeerPutTx false) .getPeerPutRx false) .getPeerPutProto false)
    .getPeerEp4 false) .getPeerEp6 false) .getPeerEpFail false
  obtain ⟨result, final, after, run, finalDevice, value⟩ :=
    (returns_iff _ _ _).mpr (dumpAllowed_front d nodes p front b tail listed nonempty resident
      ctx skb {skb with room := skb.room - 136} (hexKey p.remoteStatic) (peerFixedAttrs p)
      sequence (by dsimp; omega) (by dsimp; omega)) g before device
  refine ⟨result, final, after, ?_, finalDevice, ?_⟩
  · have source : ((getPeerDumpTailSource p ctx skb).run g).run ambient =
        ((getPeerDumpAllowedSource p ctx skb {skb with room := skb.room - 136} (hexKey p.remoteStatic)
          (peerFixedAttrs p) p.allowedipsList.head?).run g).run before := by
      simp [getPeerDumpTailSource, fresh, branch, AmbientM.branch, NlSkb.put, nlaTotal,
        r4, r40, r76, r96, r104, r116, r128, r136, Nat.sub_sub,
        endpoint, AF_INET, AF_INET6, peerFixedAttrs, before, mark]
    exact source.trans run
  · have arithmetic : skb.room - 136 - (4 + 28 * front.length) =
        skb.room - (140 + 28 * front.length) := by omega
    simpa only [arithmetic, socketFirstPeer] using value

theorem dumpTail_after_front (d : Device) (nodes : NodeId → AipNode) (p : Peer)
    (front : List NodeId) (b : NodeId) (tail : List NodeId)
    (listed : p.allowedipsList = front ++ b :: tail) (absent : b ∉ front)
    (resident : Ipv4Residents d nodes (b :: tail)) (ctx : DumpCtx) (skb : NlSkb)
    (cursor : ctx.nextAllowedip = some b) (sequence : ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 44 + 28 * (b :: tail).length ≤ skb.room) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓ result w => ⌜w.dev = some d ∧ result =
      ({ skb with room := skb.room - (44 + 28 * (b :: tail).length) },
       { ctx with nextAllowedip := none, allowedipsSeq := 0 },
       .complete (suffixLast p nodes (b :: tail)))⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let before := mark (mark (mark ambient .getPeerNoNest false)
    .getPeerPubkeyFail false) .getPeerFirst false
  obtain ⟨result, final, after, run, finalDevice, value⟩ :=
    (returns_iff _ _ _).mpr (dumpAllowed_suffix_all d nodes p ctx skb
      {skb with room := skb.room - 40} (hexKey p.remoteStatic)
      [("public_key", toJson (hexKey p.remoteStatic))] b (b :: tail) resident
      (by rw [listed]; exact cursor_after_prefix front b tail absent) (by simp) (.inr sequence)
      (by simp only [List.length_cons] at room ⊢; omega)) g before device
  refine ⟨result, final, after, ?_, finalDevice, ?_⟩
  · rw [dumpTail_resume_source p b ctx skb cursor (by simp only [List.length_cons] at room; omega)]
    simpa [branch, AmbientM.branch, before, mark] using run
  · have arithmetic : skb.room - 40 - (4 + 28 * (b :: tail).length) =
        skb.room - (44 + 28 * (b :: tail).length) := by omega
    simpa only [arithmetic, suffixLast, List.cons_append, List.nil_append] using value

end Leanux.Proofs.WG.Config
