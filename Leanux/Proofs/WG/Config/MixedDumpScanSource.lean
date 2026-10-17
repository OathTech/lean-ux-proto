import Leanux.Proofs.WG.Config.MixedDumpLeafSource
import Leanux.Proofs.WG.Config.SuffixReadbackSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- A finite readable list fits exactly according to the actual weighted puts;
node widths and repeated identifiers are unrestricted. -/
theorem suffixScan_weighted_all (d : Device) (nodes : NodeId → AipNode) (ids : List NodeId)
    (resident : ∀id ∈ ids, d.nodes[id]? = some (nodes id))
    (ctx : DumpCtx) (pubkey : String) (attrs : List (String × Json))
    (skb : NlSkb) (ips : Array Json) (room : dumpNodesSpace nodes ids ≤ skb.room) :
    Returns (suffixScan ctx pubkey attrs ids skb ips) (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧ result =
        ({skb with room := skb.room - dumpNodesSpace nodes ids},
         {ctx with nextAllowedip := none,allowedipsSeq := 0},
         .complete {publicKey := pubkey,attrs := attrs ++ [("allowed_ips",Json.arr (ips ++ dumpNodeJsons nodes ids))]})) := by
  induction ids generalizing skb ips with
  | nil =>
    intro g ambient device
    let after := {ambient with steps := ambient.steps.push {
      decision := Decision.getPeerAipIter,outcome := false,netRx := ambient.netRxSection}}
    refine ⟨_,g,after,?_,device,rfl⟩
    simp [suffixScan_nil,branch,AmbientM.branch,dumpNodeJsons,dumpNodesSpace]
    rfl
  | cons id ids ih =>
    have here := resident id (by simp)
    have tail : ∀n ∈ ids, d.nodes[n]? = some (nodes n) :=
      fun n hn => resident n (by simp [hn])
    have enough : dumpNodeSpace (nodes id) ≤ skb.room := by
      simp only [dumpNodesSpace,List.map_cons,List.sum_cons] at room
      omega
    intro g ambient device
    let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
      {a with steps := a.steps.push {decision,outcome,netRx := a.netRxSection}}
    let before := mark ambient .getPeerAipIter true
    obtain ⟨n,g1,a1,getRun,dev1,value1⟩ :=
      (returns_iff _ _ _).mpr (multipart_getNode id d _ here) g before device
    subst n
    obtain ⟨serialized,g2,a2,serializeRun,dev2,value2⟩ :=
      readNode_getAllowedips_returns (nodes id) skb (fun g => g.dev = some d) g1 a1 dev1
    simp only [ite_eq_left enough] at value2
    subst serialized
    let next := mark a2 .getPeerAipFail false
    obtain ⟨result,final,after,tailRun,finalDevice,value⟩ :=
      ih tail {skb with room := skb.room - dumpNodeSpace (nodes id)}
        (ips.push (dumpNodeJson (nodes id)))
        (by simp only [dumpNodesSpace,List.map_cons,List.sum_cons] at room; dsimp [dumpNodesSpace]; omega)
        g2 next dev2
    refine ⟨result,final,after,?_,finalDevice,?_⟩
    · have source : suffixScan ctx pubkey attrs (id :: ids) skb ips = (do
          _ ← branch .getPeerAipIter true
          let n ← liftAip (getNode id)
          let (s,ip) ← (do let (family,masked,cidr) ← readNode n; getAllowedips skb family masked cidr)
          if ← branch .getPeerAipFail ip.isNone then
            pure (s,{ctx with nextAllowedip := some id},
              .split {publicKey := pubkey,attrs := attrs ++ [("allowed_ips",Json.arr ips)],split := true})
          else suffixScan ctx pubkey attrs ids s (ips.push ip.get!)) := by
        rw [suffixScan_cons]
        simp only [bind_assoc]
        rfl
      rw [source]
      change (((liftAip (getNode id)).run g).run before >>= _) = _
      rw [getRun]
      change (((do let (family,masked,cidr) ← readNode (nodes id)
                   getAllowedips skb family masked cidr : WG.M (NlSkb × Option Json)).run g1).run a1 >>= _) = _
      rw [serializeRun]
      exact tailRun
    · simpa [dumpNodeJsons,dumpNodesSpace,Nat.sub_sub,Array.push_append,Array.append_assoc,Nat.add_comm] using value

/-- The exact first failing weighted put leaves the un-emitted identifier as
cursor. The emitted prefix may be empty, and unread tail nodes need no premise. -/
theorem suffixScan_weighted_split (d : Device) (nodes : NodeId → AipNode)
    (front : List NodeId) (next : NodeId) (tail : List NodeId)
    (resident : ∀id ∈ front ++ [next], d.nodes[id]? = some (nodes id))
    (ctx : DumpCtx) (pubkey : String) (attrs : List (String × Json))
    (skb : NlSkb) (ips : Array Json)
    (fits : dumpNodesSpace nodes front ≤ skb.room)
    (short : skb.room < dumpNodesSpace nodes front + dumpNodeSpace (nodes next)) :
    Returns (suffixScan ctx pubkey attrs (front ++ next :: tail) skb ips)
      (fun g => g.dev = some d) (fun result g => g.dev = some d ∧ result =
        ({skb with room := skb.room - dumpNodesSpace nodes front},{ctx with nextAllowedip := some next},
         .split {publicKey := pubkey,attrs := attrs ++ [("allowed_ips",Json.arr (ips ++ dumpNodeJsons nodes front))],split := true})) := by
  induction front generalizing skb ips with
  | nil =>
    have here := resident next (by simp)
    have notEnough : ¬ dumpNodeSpace (nodes next) ≤ skb.room := by
      simp only [dumpNodesSpace,List.map_nil,List.sum_nil,Nat.zero_add] at short
      omega
    intro g ambient device
    let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
      {a with steps := a.steps.push {decision,outcome,netRx := a.netRxSection}}
    let before := mark ambient .getPeerAipIter true
    obtain ⟨n,g1,a1,getRun,dev1,value1⟩ :=
      (returns_iff _ _ _).mpr (multipart_getNode next d _ here) g before device
    subst n
    obtain ⟨serialized,final,a2,serializeRun,finalDevice,value2⟩ :=
      readNode_getAllowedips_returns (nodes next) skb (fun g => g.dev = some d) g1 a1 dev1
    simp only [ite_eq_right notEnough] at value2
    subst serialized
    let after := mark a2 .getPeerAipFail true
    refine ⟨_,final,after,?_,finalDevice,rfl⟩
    have source : suffixScan ctx pubkey attrs (next :: tail) skb ips = (do
        _ ← branch .getPeerAipIter true
        let n ← liftAip (getNode next)
        let (s,ip) ← (do let (family,masked,cidr) ← readNode n; getAllowedips skb family masked cidr)
        if ← branch .getPeerAipFail ip.isNone then
          pure (s,{ctx with nextAllowedip := some next},
            .split {publicKey := pubkey,attrs := attrs ++ [("allowed_ips",Json.arr ips)],split := true})
        else suffixScan ctx pubkey attrs tail s (ips.push ip.get!)) := by
      rw [suffixScan_cons]
      simp only [bind_assoc]
      rfl
    simp only [List.nil_append]
    rw [source]
    change (((liftAip (getNode next)).run g).run before >>= _) = _
    rw [getRun]
    change (((do let (family,masked,cidr) ← readNode (nodes next)
                 getAllowedips skb family masked cidr : WG.M (NlSkb × Option Json)).run g1).run a1 >>= _) = _
    rw [serializeRun]
    simp [dumpNodesSpace,dumpNodeJsons,branch,AmbientM.branch,after,mark]
    rfl
  | cons id front ih =>
    have here := resident id (by simp)
    have others : ∀n ∈ front ++ [next], d.nodes[n]? = some (nodes n) :=
      fun n hn => resident n (by simp [hn])
    have enough : dumpNodeSpace (nodes id) ≤ skb.room := by
      simp only [dumpNodesSpace,List.map_cons,List.sum_cons] at fits
      omega
    intro g ambient device
    let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
      {a with steps := a.steps.push {decision,outcome,netRx := a.netRxSection}}
    let before := mark ambient .getPeerAipIter true
    obtain ⟨n,g1,a1,getRun,dev1,value1⟩ :=
      (returns_iff _ _ _).mpr (multipart_getNode id d _ here) g before device
    subst n
    obtain ⟨serialized,g2,a2,serializeRun,dev2,value2⟩ :=
      readNode_getAllowedips_returns (nodes id) skb (fun g => g.dev = some d) g1 a1 dev1
    simp only [ite_eq_left enough] at value2
    subst serialized
    let afterRead := mark a2 .getPeerAipFail false
    obtain ⟨result,final,after,tailRun,finalDevice,value⟩ :=
      ih others {skb with room := skb.room - dumpNodeSpace (nodes id)}
        (ips.push (dumpNodeJson (nodes id)))
        (by simp only [dumpNodesSpace,List.map_cons,List.sum_cons] at fits; dsimp [dumpNodesSpace]; omega)
        (by simp only [dumpNodesSpace,List.map_cons,List.sum_cons] at fits short; dsimp [dumpNodesSpace]; omega)
        g2 afterRead dev2
    refine ⟨result,final,after,?_,finalDevice,?_⟩
    · have source : suffixScan ctx pubkey attrs ((id :: front) ++ next :: tail) skb ips = (do
          _ ← branch .getPeerAipIter true
          let n ← liftAip (getNode id)
          let (s,ip) ← (do let (family,masked,cidr) ← readNode n; getAllowedips skb family masked cidr)
          if ← branch .getPeerAipFail ip.isNone then
            pure (s,{ctx with nextAllowedip := some id},
              .split {publicKey := pubkey,attrs := attrs ++ [("allowed_ips",Json.arr ips)],split := true})
          else suffixScan ctx pubkey attrs (front ++ next :: tail) s (ips.push ip.get!)) := by
        rw [List.cons_append,suffixScan_cons]
        simp only [bind_assoc]
        rfl
      rw [source]
      change (((liftAip (getNode id)).run g).run before >>= _) = _
      rw [getRun]
      change (((do let (family,masked,cidr) ← readNode (nodes id)
                   getAllowedips skb family masked cidr : WG.M (NlSkb × Option Json)).run g1).run a1 >>= _) = _
      rw [serializeRun]
      exact tailRun
    · simpa [dumpNodeJsons,dumpNodesSpace,Nat.sub_sub,Array.push_append,Array.append_assoc,Nat.add_comm] using value


/-- The original sequence/cursor prefix feeds the complete weighted scan.
Its selected suffix and unchanged sequence are explicit; no topology is used. -/
theorem dumpAllowed_weighted_all (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json)) (start : NodeId) (ids : List NodeId)
    (resident : ∀id ∈ ids, d.nodes[id]? = some (nodes id))
    (selected : p.allowedipsList.dropWhile (· != start) = ids) (nonempty : ids ≠ [])
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 4 + dumpNodesSpace nodes ids ≤ skb.room) :
    Returns (getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs (some start))
      (fun g => g.dev = some d) (fun result g => g.dev = some d ∧ result =
        ({skb with room := skb.room - (4 + dumpNodesSpace nodes ids)},
         {ctx with nextAllowedip := none,allowedipsSeq := 0},
         .complete {publicKey := pubkey,attrs := attrs ++ [("allowed_ips",Json.arr (dumpNodeJsons nodes ids))]})) := by
  apply (returns_iff _ _ _).mpr
  apply dumpAllowed_scan d p ctx skb0 skb pubkey attrs start ids _ selected nonempty sequence (by omega)
  apply (returns_iff _ _ _).mp
  simpa [Nat.sub_sub] using suffixScan_weighted_all d nodes ids resident
    {ctx with allowedipsSeq := d.peerAllowedips.seq} pubkey attrs
    {skb with room := skb.room - 4} #[] (by dsimp; omega)

/-- A nonempty selected suffix can split before emitting even its first node.
The allowed-IP nest has succeeded; a failed node put restores that scan skb. -/
theorem dumpAllowed_weighted_split (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json)) (start : NodeId)
    (front : List NodeId) (next : NodeId) (tail : List NodeId)
    (resident : ∀id ∈ front ++ [next], d.nodes[id]? = some (nodes id))
    (selected : p.allowedipsList.dropWhile (· != start) = front ++ next :: tail)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq)
    (fits : 4 + dumpNodesSpace nodes front ≤ skb.room)
    (short : skb.room < 4 + dumpNodesSpace nodes front + dumpNodeSpace (nodes next)) :
    Returns (getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs (some start))
      (fun g => g.dev = some d) (fun result g => g.dev = some d ∧ result =
        ({skb with room := skb.room - (4 + dumpNodesSpace nodes front)},
         {ctx with nextAllowedip := some next,allowedipsSeq := d.peerAllowedips.seq},
         .split {publicKey := pubkey,attrs := attrs ++ [("allowed_ips",Json.arr (dumpNodeJsons nodes front))],split := true})) := by
  apply (returns_iff _ _ _).mpr
  apply dumpAllowed_scan d p ctx skb0 skb pubkey attrs start (front ++ next :: tail) _
    selected (by simp) sequence (by omega)
  apply (returns_iff _ _ _).mp
  simpa [Nat.sub_sub] using suffixScan_weighted_split d nodes front next tail resident
    {ctx with allowedipsSeq := d.peerAllowedips.seq} pubkey attrs
    {skb with room := skb.room - 4} #[] (by dsimp; omega) (by dsimp; omega)

end Leanux.Proofs.WG.Config
