import Leanux.Proofs.WG.Config.SuffixReadbackFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- The original allowed-IP loop and its completion, with the accumulated IPs
explicit for induction. All original node reads, guards and split exits remain. -/
def suffixScan (ctx : DumpCtx) (pubkey : String) (attrs : List (String × Json))
    (ids : List NodeId) (skb : NlSkb) (ips : Array Json) : WG.M PeerDumpResult := do
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

theorem suffixScan_all (d : Device) (nodes : NodeId → AipNode) (ids : List NodeId)
    (resident : Ipv4Residents d nodes ids) (ctx : DumpCtx) (pubkey : String)
    (attrs : List (String × Json)) (skb : NlSkb) (ips : Array Json)
    (room : 28 * ids.length ≤ skb.room) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ suffixScan ctx pubkey attrs ids skb ips
    ⦃⇓ result w => ⌜w.dev = some d ∧ result =
      ({ skb with room := skb.room - 28 * ids.length },
       { ctx with nextAllowedip := none, allowedipsSeq := 0 },
       .complete { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr (ips ++ ipv4Jsons nodes ids))] })⌝⦄ := by
  induction ids generalizing skb ips with
  | nil =>
    apply (returns_iff _ _ _).mp
    intro g ambient device
    let after := {ambient with steps := ambient.steps.push {
      decision := Decision.getPeerAipIter, outcome := false, netRx := ambient.netRxSection}}
    refine ⟨_, g, after, ?_, device, rfl⟩
    simp [suffixScan_nil, branch, AmbientM.branch, ipv4Jsons]
    rfl
  | cons id ids ih =>
    have here := resident id (by simp)
    have tail : Ipv4Residents d nodes ids := fun n hn => resident n (by simp [hn])
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
        (by change 28 ≤ skb.room; simp only [List.length_cons] at room; omega)
        (fun g => g.dev = some d)) g2 a2 dev2
    subst serialized
    let next := mark a3 .getPeerAipFail false
    obtain ⟨result, final, after, tailRun, finalDevice, value⟩ :=
      (returns_iff _ _ _).mpr (ih tail {skb with room := skb.room - 28}
        (ips.push (ipv4NodeJson (nodes id)))
        (by simp only [List.length_cons] at room; dsimp; omega)) g3 next dev3
    refine ⟨result, final, after, ?_, finalDevice, ?_⟩
    · have getLift (nid : NodeId) : (monadLift (getNode nid) : WG.M AipNode) =
          liftAip (getNode nid) := rfl
      simp only [suffixScan_cons, getLift]
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

theorem dumpAllowed_scan (d : Device) (p : Peer) (ctx : DumpCtx)
    (skb0 skb : NlSkb) (pubkey : String) (attrs : List (String × Json))
    (start : NodeId) (ids : List NodeId) (expected : PeerDumpResult)
    (selected : p.allowedipsList.dropWhile (· != start) = ids) (nonempty : ids ≠ [])
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 4 ≤ skb.room)
    (scan : ⦃fun w => ⌜w.dev = some d⌝⦄
      suffixScan { ctx with allowedipsSeq := d.peerAllowedips.seq } pubkey attrs ids
        { skb with room := skb.room - 4 } #[]
      ⦃⇓ result w => ⌜w.dev = some d ∧ result = expected⌝⦄) :
    ⦃fun w => ⌜w.dev = some d⌝⦄
      getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs (some start)
    ⦃⇓ result w => ⌜w.dev = some d ∧ result = expected⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let a0 := mark ambient .getPeerNoAips false
  let a1 := mark a0 .getPeerSeqUnset (ctx.allowedipsSeq == 0)
  let a2 := if ctx.allowedipsSeq = 0 then a1 else mark a1 .getPeerSeqChanged false
  let before := mark a2 .getPeerAipsNestFail false
  obtain ⟨result, final, after, run, finalDevice, value⟩ :=
    (returns_iff _ _ _).mpr scan g before device
  refine ⟨result, final, after, ?_, finalDevice, value⟩
  rw [dumpAllowed_suffix_source]
  have enough : ¬ skb.room < 4 := by omega
  by_cases zero : ctx.allowedipsSeq = 0
  · simpa [branch, AmbientM.branch, getDev, device, selected, nonempty,
      NlSkb.put, nlaTotal, enough, zero, before, a2, a1, a0, mark] using run
  · have stable : ctx.allowedipsSeq = d.peerAllowedips.seq := sequence.resolve_left zero
    have nonzero : d.peerAllowedips.seq ≠ 0 := by intro eq; exact zero (stable.trans eq)
    have unchanged : {ctx with allowedipsSeq := d.peerAllowedips.seq} = ctx := by
      cases ctx; simp_all
    simpa [branch, AmbientM.branch, getDev, device, selected, nonempty,
      NlSkb.put, nlaTotal, enough, stable, nonzero, before, a2, a1, a0, mark,
      unchanged] using run

theorem suffixScan_split_one (d : Device) (nodes : NodeId → AipNode)
    (a b : NodeId) (tail : List NodeId) (ctx : DumpCtx) (pubkey : String)
    (attrs : List (String × Json)) (skb : NlSkb)
    (resident : Ipv4Residents d nodes [a, b]) (room : skb.room = 28) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ suffixScan ctx pubkey attrs (a :: b :: tail) skb #[]
    ⦃⇓ result w => ⌜w.dev = some d ∧ result =
      ({ skb with room := 0 }, { ctx with nextAllowedip := some b },
        .split { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr #[ipv4NodeJson (nodes a)])], split := true })⌝⦄ := by
  have ra := resident a (by simp)
  have rb := resident b (by simp)
  apply (returns_iff _ _ _).mp
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let before := mark ambient .getPeerAipIter true
  obtain ⟨n1, g1, a1, get1, dev1, val1⟩ :=
    (returns_iff _ _ _).mpr (multipart_getNode a d _ ra.1) g before device
  subst n1
  obtain ⟨r1, g2, a2, read1, dev2, rval1⟩ :=
    (returns_iff _ _ _).mpr (readNode_ipv4_native (nodes a) ra.2
      (fun g => g.dev = some d)) g1 a1 dev1
  subst r1
  obtain ⟨s1, g3, a3, ser1, dev3, sval1⟩ :=
    (returns_iff _ _ _).mpr (getAllowedips_inserted true (nodes a).bits (nodes a).cidr
      skb (by change 28 ≤ skb.room; omega) (fun g => g.dev = some d)) g2 a2 dev2
  subst s1
  let middle := mark (mark a3 .getPeerAipFail false) .getPeerAipIter true
  obtain ⟨n2, g4, a4, get2, dev4, val2⟩ :=
    (returns_iff _ _ _).mpr (multipart_getNode b d _ rb.1) g3 middle dev3
  subst n2
  obtain ⟨r2, g5, a5, read2, dev5, rval2⟩ :=
    (returns_iff _ _ _).mpr (readNode_ipv4_native (nodes b) rb.2
      (fun g => g.dev = some d)) g4 a4 dev4
  subst r2
  obtain ⟨s2, g6, a6, ser2, dev6, sval2⟩ :=
    (returns_iff _ _ _).mpr (getAllowedips_zero_native {skb with room := 0}
      4 (allowedMasked true (nodes b).bits (nodes b).cidr) (nodes b).cidr rfl
      (fun g => g.dev = some d)) g5 a5 dev5
  subst s2
  let after := mark a6 .getPeerAipFail true
  refine ⟨_, g6, after, ?_, dev6, rfl⟩
  have getLift (nid : NodeId) : (monadLift (getNode nid) : WG.M AipNode) =
      liftAip (getNode nid) := rfl
  simp only [suffixScan_cons, getLift]
  simp [branch, AmbientM.branch, room, mark, before, middle, after,
    allowedFamily, allowedIpSpace, nlaTotal, ipv4NodeJson] at get1 read1 ser1 get2 read2 ser2 ⊢
  rw [get1]
  dsimp only [bind, Except.bind]
  rw [read1]
  dsimp only [bind, Except.bind]
  rw [ser1]
  simp only [Option.isNone, Option.get!, reduceCtorEq, ↓reduceIte]
  dsimp only [Pure.pure, Except.pure, Bind.bind, Except.bind, StateT.run, StateT.bind, StateT.pure,
    liftM, monadLift, MonadLift.monadLift, StateT.lift, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, Functor.map, StateT.map, Except.map]
  dsimp only [StateT.run] at get2 read2 ser2
  rw [get2]
  dsimp only [bind, Except.bind]
  rw [read2]
  dsimp only [bind, Except.bind]
  rw [ser2]
  rfl

theorem dumpAllowed_suffix_all (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json)) (start : NodeId) (ids : List NodeId)
    (resident : Ipv4Residents d nodes ids)
    (selected : p.allowedipsList.dropWhile (· != start) = ids) (nonempty : ids ≠ [])
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 4 + 28 * ids.length ≤ skb.room) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs (some start)
    ⦃⇓ result w => ⌜w.dev = some d ∧ result =
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
    ⦃fun w => ⌜w.dev = some d⌝⦄ getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs (some a)
    ⦃⇓ result w => ⌜w.dev = some d ∧ result =
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
    ⦃fun w => ⌜w.dev = some d⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓ result w => ⌜w.dev = some d ∧ result =
      ({ skb with room := 0 }, { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq },
       .split (multipartFirst p (nodes a).bits (nodes a).cidr))⌝⦄ := by
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
    (returns_iff _ _ _).mpr (dumpAllowed_suffix_split d nodes p a b tail
      ctx skb {skb with room := 32} (hexKey p.remoteStatic) (peerFixedAttrs p)
      listed resident sequence rfl) g before device
  refine ⟨result, final, after, ?_, finalDevice, ?_⟩
  · have source : ((getPeerDumpTailSource p ctx skb).run g).run ambient =
        ((getPeerDumpAllowedSource p ctx skb {skb with room := 32} (hexKey p.remoteStatic)
          (peerFixedAttrs p) (some a)).run g).run before := by
      simp [getPeerDumpTailSource, fresh, listed, branch, AmbientM.branch, NlSkb.put,
        nlaTotal, room, endpoint, AF_INET, AF_INET6, peerFixedAttrs, before, mark]
    exact source.trans run
  · simpa [multipartFirst, ipv4NodeJson] using value

theorem dumpTail_suffix_resume (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (a b : NodeId) (tail : List NodeId) (ctx : DumpCtx) (skb : NlSkb)
    (listed : p.allowedipsList = a :: b :: tail) (distinct : a ≠ b)
    (resident : Ipv4Residents d nodes (b :: tail))
    (cursor : ctx.nextAllowedip = some b) (sequence : ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 44 + 28 * (1 + tail.length) ≤ skb.room) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓ result w => ⌜w.dev = some d ∧ result =
      ({ skb with room := skb.room - (44 + 28 * (1 + tail.length)) },
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
      (by simp [listed, distinct]) (by simp) (.inr sequence)
      (by simp only [List.length_cons]; omega)) g before device
  refine ⟨result, final, after, ?_, finalDevice, ?_⟩
  · rw [dumpTail_resume_source p b ctx skb cursor (by omega)]
    simpa [branch, AmbientM.branch, before, mark] using run
  · have arithmetic : skb.room - 40 - (4 + 28 * (b :: tail).length) =
        skb.room - (44 + 28 * (1 + tail.length)) := by
      simp only [List.length_cons]
      omega
    simpa only [arithmetic, suffixLast, List.cons_append, List.nil_append] using value

end Leanux.Proofs.WG.Config
