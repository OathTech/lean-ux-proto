import Leanux.Proofs.WG.Config.MultipartLeaves
import Leanux.Proofs.WG.Config.AllowedReadbackSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem dumpAllowed_two_split (d : Device) (p : Peer) (a b : NodeId)
    (pid : PeerId) (addr₁ cidr₁ addr₂ cidr₂ : Nat) (parent₁ parent₂ : Slot)
    (ctx : DumpCtx) (skb0 skb : NlSkb) (pubkey : String) (attrs : List (String × Json))
    (listed : p.allowedipsList = [a, b])
    (firstNode : d.nodes[a]? = some { newNode addr₁ cidr₁ 32 (some pid) with parent := parent₁ })
    (secondNode : d.nodes[b]? = some { newNode addr₂ cidr₂ 32 (some pid) with parent := parent₂ })
    (sequence : ctx.allowedipsSeq = 0) (room : skb.room = 32) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs (some a)
    ⦃⇓ result w => ⌜w.dev = some d ∧ result =
      ({ skb with room := 0 }, { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq },
       .split { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr #[allowedJson true addr₁ cidr₁])], split := true })⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let before := mark (mark (mark (mark ambient .getPeerNoAips false)
    .getPeerSeqUnset true) .getPeerAipsNestFail false) .getPeerAipIter true
  obtain ⟨n1, g1, a1, get1, dev1, val1⟩ :=
    (returns_iff _ _ _).mpr (multipart_getNode a d _ firstNode) g before device
  subst n1
  obtain ⟨r1, g2, a2, read1, dev2, rval1⟩ :=
    (returns_iff _ _ _).mpr (readInsertedNode true addr₁ cidr₁ pid parent₁
      (fun g => g.dev = some d)) g1 a1 dev1
  subst r1
  obtain ⟨s1, g3, a3, ser1, dev3, sval1⟩ :=
    (returns_iff _ _ _).mpr (getAllowedips_inserted true addr₁ cidr₁
      {skb with room := 28} (by change 28 ≤ 28; decide) (fun g => g.dev = some d)) g2 a2 dev2
  subst s1
  let middle := mark (mark a3 .getPeerAipFail false) .getPeerAipIter true
  obtain ⟨n2, g4, a4, get2, dev4, val2⟩ :=
    (returns_iff _ _ _).mpr (multipart_getNode b d _ secondNode) g3 middle dev3
  subst n2
  obtain ⟨r2, g5, a5, read2, dev5, rval2⟩ :=
    (returns_iff _ _ _).mpr (readInsertedNode true addr₂ cidr₂ pid parent₂
      (fun g => g.dev = some d)) g4 a4 dev4
  subst r2
  obtain ⟨s2, g6, a6, ser2, dev6, sval2⟩ :=
    (returns_iff _ _ _).mpr (getAllowedips_zero_native {skb with room := 0}
      4 (allowedMasked true addr₂ cidr₂) cidr₂ rfl (fun g => g.dev = some d)) g5 a5 dev5
  subst s2
  let after := mark a6 .getPeerAipFail true
  refine ⟨_, g6, after, ?_, dev6, rfl⟩
  have getLift (nid : NodeId) : (monadLift (getNode nid) : WG.M AipNode) =
      liftAip (getNode nid) := rfl
  simp only [getPeerDumpAllowedSource, getLift]
  simp [listed, List.forIn_cons, List.forIn_nil, NlSkb.put, nlaTotal, room,
    branch, AmbientM.branch, getDev, device, sequence,
    mark, before, middle, after, allowedBits, allowedFamily, allowedIpSpace] at get1 read1 ser1 get2 read2 ser2 ⊢
  rw [get1]
  dsimp only [bind, Except.bind]
  rw [read1]
  dsimp only [bind, Except.bind]
  rw [ser1]
  dsimp only [bind, Except.bind]
  simp only [reduceCtorEq, ↓reduceIte]
  simp only [Option.isNone, Option.get!, StateT.run_pure]
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

theorem dumpTail_two_split (d : Device) (p : Peer) (a b : NodeId)
    (pid : PeerId) (addr₁ cidr₁ addr₂ cidr₂ : Nat) (parent₁ parent₂ : Slot)
    (ctx : DumpCtx) (skb : NlSkb)
    (listed : p.allowedipsList = [a, b]) (endpoint : p.endpoint = none)
    (firstNode : d.nodes[a]? = some { newNode addr₁ cidr₁ 32 (some pid) with parent := parent₁ })
    (secondNode : d.nodes[b]? = some { newNode addr₂ cidr₂ 32 (some pid) with parent := parent₂ })
    (fresh : ctx.nextAllowedip = none) (sequence : ctx.allowedipsSeq = 0) (room : skb.room = 168) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓ result w => ⌜w.dev = some d ∧ result =
      ({ skb with room := 0 }, { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq },
       .split (multipartFirst p addr₁ cidr₁))⌝⦄ := by
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
    (returns_iff _ _ _).mpr (dumpAllowed_two_split d p a b pid addr₁ cidr₁ addr₂ cidr₂
      parent₁ parent₂ ctx skb {skb with room := 32} (hexKey p.remoteStatic) (peerFixedAttrs p)
      listed firstNode secondNode sequence rfl) g before device
  refine ⟨result, final, after, ?_, finalDevice, ?_⟩
  · have source : ((getPeerDumpTailSource p ctx skb).run g).run ambient =
        ((getPeerDumpAllowedSource p ctx skb {skb with room := 32} (hexKey p.remoteStatic)
          (peerFixedAttrs p) (some a)).run g).run before := by
      simp [getPeerDumpTailSource, fresh, listed, branch, AmbientM.branch, NlSkb.put,
        nlaTotal, room, endpoint, AF_INET, AF_INET6, peerFixedAttrs, before, mark]
    exact source.trans run
  · simpa [multipartFirst] using value

theorem dumpAllowed_resume (d : Device) (p : Peer) (a b : NodeId) (pid : PeerId)
    (addr cidr : Nat) (parent : Slot) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json))
    (listed : p.allowedipsList = [a, b]) (distinct : a ≠ b)
    (node : d.nodes[b]? = some { newNode addr cidr 32 (some pid) with parent })
    (sequence : ctx.allowedipsSeq = d.peerAllowedips.seq) (room : 32 ≤ skb.room) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs (some b)
    ⦃⇓ result w => ⌜w.dev = some d ∧ result =
      ({ skb with room := skb.room - 32 }, { ctx with nextAllowedip := none, allowedipsSeq := 0 },
       .complete { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr #[allowedJson true addr cidr])] })⌝⦄ := by
  have source : getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs (some b) =
      getPeerDumpAllowedSource {p with allowedipsList := [b]} ctx skb0 skb pubkey attrs (some b) := by
    simp [getPeerDumpAllowedSource, listed, distinct]
  rw [source]
  simpa [allowedBits, allowedFamily, allowedIpSpace, nlaTotal, Nat.sub_sub] using
    dumpAllowed_single true d {p with allowedipsList := [b]} b pid addr cidr parent
      ctx skb0 skb pubkey attrs rfl node (Or.inr sequence) room

theorem dumpTail_resume (d : Device) (p : Peer) (a b : NodeId) (pid : PeerId)
    (addr cidr : Nat) (parent : Slot) (ctx : DumpCtx) (skb : NlSkb)
    (listed : p.allowedipsList = [a, b]) (distinct : a ≠ b)
    (node : d.nodes[b]? = some { newNode addr cidr 32 (some pid) with parent })
    (cursor : ctx.nextAllowedip = some b) (sequence : ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 72 ≤ skb.room) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓ result w => ⌜w.dev = some d ∧ result =
      ({ skb with room := skb.room - 72 }, { ctx with nextAllowedip := none, allowedipsSeq := 0 },
       .complete (multipartLast p addr cidr))⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient device
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let before := mark (mark (mark ambient .getPeerNoNest false)
    .getPeerPubkeyFail false) .getPeerFirst false
  obtain ⟨result, final, after, run, finalDevice, value⟩ :=
    (returns_iff _ _ _).mpr (dumpAllowed_resume d p a b pid addr cidr parent ctx skb
      {skb with room := skb.room - 40} (hexKey p.remoteStatic)
      [("public_key", toJson (hexKey p.remoteStatic))] listed distinct node sequence
      (by dsimp; omega)) g before device
  refine ⟨result, final, after, ?_, finalDevice, ?_⟩
  · rw [dumpTail_resume_source p b ctx skb cursor room]
    simpa [branch, AmbientM.branch, before, mark] using run
  · simpa [multipartLast, Nat.sub_sub] using value

end Leanux.Proofs.WG.Config
