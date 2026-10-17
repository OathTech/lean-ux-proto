import Leanux.Proofs.WG.Config.MultipartLeaves
import Leanux.Proofs.WG.Config.MultipartModel
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
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs (some a)
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
      ({ skb with room := 0 }, { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq },
       .split { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr #[allowedJson true addr₁ cidr₁])], split := true })⌝⦄ := by
  have hn₁ := readInsertedNode true addr₁ cidr₁ pid parent₁ (fun k => k.wg = some d)
  have hn₂ := readInsertedNode true addr₂ cidr₂ pid parent₂ (fun k => k.wg = some d)
  have hg₁ := multipart_getNode a d _ firstNode
  have hg₂ := multipart_getNode b d _ secondNode
  have ha := getAllowedips_inserted true addr₁ cidr₁ { skb with room := 28 }
    (by change allowedIpSpace 4 ≤ 28; decide) (fun k => k.wg = some d)
  have hz := getAllowedips_zero { skb with room := 0 } 4 (allowedMasked true addr₂ cidr₂)
    cidr₂ rfl (fun k => k.wg = some d)
  have hb := branch_state_returns (fun k => k.wg = some d)
  simp [getPeerDumpAllowedSource, listed, List.forIn_cons, List.forIn_nil,
    NlSkb.put, nlaTotal, room, bind_assoc]
  mvcgen [getDev, getK, invariant, hb, hg₁, hg₂, hn₁, hn₂, ha, hz]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [sequence, allowedBits, allowedFamily, allowedIpSpace, nlaTotal]
  all_goals subst_vars
  all_goals mvcgen [hn₁, hn₂, ha, hz, branch, hg₁, hg₂]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [allowedBits, allowedFamily, allowedIpSpace, nlaTotal]
  all_goals subst_vars
  all_goals mvcgen [hn₁, hn₂, ha, hz, branch, hg₁, hg₂]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [allowedBits, allowedFamily, allowedIpSpace, nlaTotal]
  all_goals subst_vars
  all_goals mvcgen [hn₁, hn₂, ha, hz, branch, hg₁, hg₂]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [allowedBits, allowedFamily, allowedIpSpace, nlaTotal]
  all_goals subst_vars
  all_goals mvcgen [hn₁, hn₂, ha, hz, branch, hg₁, hg₂]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [allowedBits, allowedFamily, allowedIpSpace, nlaTotal]
  all_goals subst_vars
  all_goals mvcgen [hn₁, hn₂, ha, hz, branch, hg₁, hg₂]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [allowedBits, allowedFamily, allowedIpSpace, nlaTotal]
  all_goals subst_vars
  all_goals mvcgen [hn₁, hn₂, ha, hz, branch, hg₁, hg₂]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [allowedBits, allowedFamily, allowedIpSpace, nlaTotal]


theorem dumpTail_two_split (d : Device) (p : Peer) (a b : NodeId)
    (pid : PeerId) (addr₁ cidr₁ addr₂ cidr₂ : Nat) (parent₁ parent₂ : Slot)
    (ctx : DumpCtx) (skb : NlSkb)
    (listed : p.allowedipsList = [a, b]) (endpoint : p.endpoint = none)
    (firstNode : d.nodes[a]? = some { newNode addr₁ cidr₁ 32 (some pid) with parent := parent₁ })
    (secondNode : d.nodes[b]? = some { newNode addr₂ cidr₂ 32 (some pid) with parent := parent₂ })
    (fresh : ctx.nextAllowedip = none) (sequence : ctx.allowedipsSeq = 0) (room : skb.room = 168) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
      ({ skb with room := 0 }, { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq },
       .split (multipartFirst p addr₁ cidr₁))⌝⦄ := by
  have ha := dumpAllowed_two_split d p a b pid addr₁ cidr₁ addr₂ cidr₂ parent₁ parent₂
    ctx skb { skb with room := 32 } (hexKey p.remoteStatic) (peerFixedAttrs p)
    listed firstNode secondNode sequence rfl
  simp only [getPeerDumpTailSource, fresh]
  simp [NlSkb.put, nlaTotal, room, endpoint, AF_INET, AF_INET6, listed]
  mvcgen [branch, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerFixedAttrs, endpoint, multipartFirst]
  all_goals subst_vars
  all_goals mvcgen [ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [peerFixedAttrs, endpoint, multipartFirst]

theorem dumpAllowed_resume (d : Device) (p : Peer) (a b : NodeId) (pid : PeerId)
    (addr cidr : Nat) (parent : Slot) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json))
    (listed : p.allowedipsList = [a, b]) (distinct : a ≠ b)
    (node : d.nodes[b]? = some { newNode addr cidr 32 (some pid) with parent })
    (sequence : ctx.allowedipsSeq = d.peerAllowedips.seq) (room : 32 ≤ skb.room) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs (some b)
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
      ({ skb with room := skb.room - 32 }, { ctx with nextAllowedip := none, allowedipsSeq := 0 },
       .complete { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr #[allowedJson true addr cidr])] })⌝⦄ := by
  have hn := readInsertedNode true addr cidr pid parent (fun k => k.wg = some d)
  have hg := multipart_getNode b d _ node
  have ha := getAllowedips_inserted true addr cidr { skb with room := skb.room - 4 }
    (by change 28 ≤ skb.room - 4; omega) (fun k => k.wg = some d)
  simp [getPeerDumpAllowedSource, listed, distinct, List.forIn_cons, List.forIn_nil,
    NlSkb.put, nlaTotal, show ¬ skb.room < 4 by omega, bind_assoc]
  mvcgen [getDev, getK, invariant, branch, hg, hn, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [sequence, allowedBits, allowedFamily, allowedIpSpace, nlaTotal, Nat.sub_sub]
  all_goals subst_vars
  all_goals mvcgen [hn, ha, branch, hg]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [allowedBits, allowedFamily, allowedIpSpace, nlaTotal, Nat.sub_sub]
  all_goals subst_vars
  all_goals mvcgen [hn, ha, branch, hg]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [allowedBits, allowedFamily, allowedIpSpace, nlaTotal, Nat.sub_sub]
  all_goals subst_vars
  all_goals mvcgen [ha, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [allowedBits, allowedFamily, allowedIpSpace, nlaTotal, Nat.sub_sub]


theorem dumpTail_resume (d : Device) (p : Peer) (a b : NodeId) (pid : PeerId)
    (addr cidr : Nat) (parent : Slot) (ctx : DumpCtx) (skb : NlSkb)
    (listed : p.allowedipsList = [a, b]) (distinct : a ≠ b)
    (node : d.nodes[b]? = some { newNode addr cidr 32 (some pid) with parent })
    (cursor : ctx.nextAllowedip = some b) (sequence : ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 72 ≤ skb.room) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
      ({ skb with room := skb.room - 72 }, { ctx with nextAllowedip := none, allowedipsSeq := 0 },
       .complete (multipartLast p addr cidr))⌝⦄ := by
  have ha := dumpAllowed_resume d p a b pid addr cidr parent ctx skb { skb with room := skb.room - 40 }
    (hexKey p.remoteStatic) [("public_key", toJson (hexKey p.remoteStatic))]
    listed distinct node sequence (by dsimp; omega)
  rw [dumpTail_resume_source p b ctx skb cursor room]
  mvcgen [branch, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [multipartLast, Nat.sub_sub]

end Leanux.Proofs.WG.Config
