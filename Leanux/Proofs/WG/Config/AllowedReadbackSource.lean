import Leanux.Proofs.WG.Config.AllowedReadbackLeaves

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem dumpAllowed_single (v4 : Bool) (d : Device) (p : Peer) (id : NodeId)
    (pid : PeerId) (addr cidr : Nat) (parent : Slot) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json))
    (listed : p.allowedipsList = [id])
    (node : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) (some pid) with parent })
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 4 + allowedIpSpace (allowedFamily v4) ≤ skb.room) :
    ⦃fun g => ⌜g.dev = some d⌝⦄ getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs (some id)
    ⦃⇓ result g => ⌜g.dev = some d ∧ result =
      ({ skb with room := skb.room - (4 + allowedIpSpace (allowedFamily v4)) },
       { ctx with nextAllowedip := none, allowedipsSeq := 0 },
       .complete { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr #[allowedJson v4 addr cidr])] })⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let a0 := mark ambient .getPeerNoAips false
  let a1 := mark a0 .getPeerSeqUnset (ctx.allowedipsSeq == 0)
  let a2 := if ctx.allowedipsSeq = 0 then a1 else mark a1 .getPeerSeqChanged false
  let before := mark (mark a2 .getPeerAipsNestFail false) .getPeerAipIter true
  let g1 := {g with dev := some d}
  let n := {newNode addr cidr (allowedBits v4) (some pid) with parent}
  have getRun : ((liftAip (getNode id)).run g).run before = .ok ((n, g1), before) := by
    simp [liftAip, getNode, getDev, modifyDev, device, node, g1, n]
    rfl
  obtain ⟨read, g2, a3, readRun, dev2, readValue⟩ :=
    (returns_iff _ _ _).mpr (readInsertedNode v4 addr cidr pid parent
      (fun g => g.dev = some d)) g1 before rfl
  subst read
  obtain ⟨serialized, g3, a4, serializeRun, dev3, serializedValue⟩ :=
    (returns_iff _ _ _).mpr (getAllowedips_inserted v4 addr cidr
      {skb with room := skb.room - 4} (by dsimp; omega) (fun g => g.dev = some d))
      g2 a3 dev2
  subst serialized
  let after := mark (mark a4 .getPeerAipFail false) .getPeerAipIter false
  refine ⟨_, g3, after, ?_, dev3, rfl⟩
  have getLift (nid : NodeId) : (monadLift (getNode nid) : WG.M AipNode) =
      liftAip (getNode nid) := rfl
  simp only [getPeerDumpAllowedSource, getLift]
  have room4 : ¬ skb.room < 4 := by omega
  by_cases zero : ctx.allowedipsSeq = 0
  · simp [listed, List.forIn_cons, List.forIn_nil, NlSkb.put, nlaTotal, room4,
      branch, AmbientM.branch, getDev, device, zero,
      mark, a0, a1, a2, before, after, Nat.sub_sub] at getRun readRun serializeRun ⊢
    rw [getRun]
    dsimp only [bind, Except.bind]
    rw [readRun]
    dsimp only [bind, Except.bind]
    rw [serializeRun]
    rfl
  · have stable : ctx.allowedipsSeq = d.peerAllowedips.seq := sequence.resolve_left zero
    have deviceNonzero : d.peerAllowedips.seq ≠ 0 := by
      intro isZero
      exact zero (stable.trans isZero)
    simp [listed, List.forIn_cons, List.forIn_nil, NlSkb.put, nlaTotal, room4,
      branch, AmbientM.branch, getDev, device, stable, deviceNonzero,
      mark, a0, a1, a2, before, after, Nat.sub_sub] at getRun readRun serializeRun ⊢
    rw [getRun]
    dsimp only [bind, Except.bind]
    rw [readRun]
    dsimp only [bind, Except.bind]
    rw [serializeRun]
    rfl

theorem dumpTail_single (v4 : Bool) (d : Device) (p : Peer) (id : NodeId)
    (pid : PeerId) (addr cidr : Nat) (parent : Slot) (ctx : DumpCtx) (skb : NlSkb)
    (listed : p.allowedipsList = [id])
    (node : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) (some pid) with parent })
    (fresh : ctx.nextAllowedip = none)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 172 + allowedIpSpace (allowedFamily v4) ≤ skb.room) :
    ⦃fun g => ⌜g.dev = some d⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓ result g => ⌜g.dev = some d ∧ result =
      ({ skb with room := skb.room - (peerFixedSpace p + 4 + allowedIpSpace (allowedFamily v4)) },
       { ctx with nextAllowedip := none, allowedipsSeq := 0 },
       .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs p ++ [("allowed_ips", Json.arr #[allowedJson v4 addr cidr])] })⌝⦄ := by
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
  have space : peerFixedSpace p ≤ 168 := by
    unfold peerFixedSpace
    split
    · omega
    · split <;> omega
  apply (returns_iff _ _ _).mp
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let markedPrefix := mark (mark (mark (mark (mark (mark (mark (mark (mark ambient
    .getPeerNoNest false) .getPeerPubkeyFail false) .getPeerFirst true)
    .getPeerPskFail false) .getPeerPutHandshake false) .getPeerPutKeepalive false)
    .getPeerPutTx false) .getPeerPutRx false) .getPeerPutProto false
  let family := (p.endpoint.map (·.family)).getD 0
  let ep := mark markedPrefix .getPeerEp4 (family == AF_INET)
  let before := mark (if family = AF_INET then ep else
    mark ep .getPeerEp6 (family == AF_INET6)) .getPeerEpFail false
  let reduced := {skb with room := skb.room - peerFixedSpace p}
  obtain ⟨result, final, after, run, finalDevice, value⟩ :=
    (returns_iff _ _ _).mpr
      (dumpAllowed_single v4 d p id pid addr cidr parent ctx skb reduced
        (hexKey p.remoteStatic) (peerFixedAttrs p) listed node sequence (by dsimp [reduced]; omega))
      g before device
  refine ⟨result, final, after, ?_, finalDevice, ?_⟩
  · have source : ((getPeerDumpTailSource p ctx skb).run g).run ambient =
        ((getPeerDumpAllowedSource p ctx skb reduced (hexKey p.remoteStatic)
          (peerFixedAttrs p) (some id)).run g).run before := by
      by_cases ep4 : (p.endpoint.map (·.family)).getD 0 = AF_INET <;>
        by_cases ep6 : (p.endpoint.map (·.family)).getD 0 = AF_INET6
      all_goals
        simp [getPeerDumpTailSource, fresh, listed, branch, AmbientM.branch,
          NlSkb.put, nlaTotal, Nat.sub_sub, r4, r40, r76, r96, r104, r116, r128,
          r136, r156, r168, ep4, ep6, peerFixedSpace, peerFixedAttrs,
          reduced, before, ep, markedPrefix, family, mark]
      all_goals cases p.endpoint <;> rfl
    exact source.trans run
  · simpa [reduced, Nat.sub_sub, Nat.add_assoc] using value

theorem getPeerDump_single (v4 : Bool) (d : Device) (p : Peer) (id : NodeId)
    (pid : PeerId) (addr cidr : Nat) (parent : Slot) (ctx : DumpCtx) (skb : NlSkb)
    (resident : d.peers[pid]? = some p) (listed : p.allowedipsList = [id])
    (node : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) (some pid) with parent })
    (fresh : ctx.nextAllowedip = none)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 172 + allowedIpSpace (allowedFamily v4) ≤ skb.room) :
    Returns (getPeerDump pid ctx skb) (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧ result =
        ({ skb with room := skb.room - (peerFixedSpace p + 4 + allowedIpSpace (allowedFamily v4)) },
         { ctx with nextAllowedip := none, allowedipsSeq := 0 },
         .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs p ++ [("allowed_ips", Json.arr #[allowedJson v4 addr cidr])] })) := by
  have hg : Returns (getPeer pid) (fun g => g.dev = some d)
      (fun q g => q = p ∧ g.dev = some d) := by
    intro g ambient device
    refine ⟨p, g, ambient, ?_, rfl, device⟩
    simp [getPeer, getDev, device, resident]
    rfl
  rw [getPeerDump_source]
  apply returns_bind _ _ hg
  intro q g ambient h
  obtain ⟨same, hd⟩ := h
  subst q
  exact (returns_iff _ _ _).mpr
    (dumpTail_single v4 d p id pid addr cidr parent ctx skb listed node fresh sequence room) g ambient hd

end Leanux.Proofs.WG.Config
