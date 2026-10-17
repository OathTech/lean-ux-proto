import Leanux.Proofs.WG.Config.AllowedInsertSource
import Leanux.Proofs.WG.Config.DumpReturns

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem readInsertedNode (v4 : Bool) (addr cidr : Nat) (pid : PeerId)
    (parent : Slot) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ readNode { newNode addr cidr (allowedBits v4) (some pid) with parent }
    ⦃⇓ result w => ⌜P w.k ∧ result = (allowedFamily v4, allowedMasked v4 addr cidr, cidr)⌝⦄ := by
  cases v4
  all_goals mvcgen [readNode, swapEndian, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [newNode, allowedBits, allowedFamily, allowedMasked]
  all_goals grind only

theorem getAllowedips_inserted (v4 : Bool) (addr cidr : Nat) (skb : NlSkb)
    (room : allowedIpSpace (allowedFamily v4) ≤ skb.room) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ getAllowedips skb (allowedFamily v4) (allowedMasked v4 addr cidr) cidr
    ⦃⇓ result w => ⌜P w.k ∧ result =
      ({ skb with room := skb.room - allowedIpSpace (allowedFamily v4) },
        some (allowedJson v4 addr cidr))⌝⦄ := by
  cases v4
  all_goals mvcgen [getAllowedips, NlSkb.put, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [allowedIpSpace, allowedFamily, allowedJson, nlaTotal, Nat.sub_sub]
  all_goals split at * <;> simp_all
  all_goals try simp_all [Nat.sub_sub]
  all_goals grind only

theorem dumpAllowed_single (v4 : Bool) (d : Device) (p : Peer) (id : NodeId)
    (pid : PeerId) (addr cidr : Nat) (parent : Slot) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json))
    (listed : p.allowedipsList = [id])
    (node : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) (some pid) with parent })
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 4 + allowedIpSpace (allowedFamily v4) ≤ skb.room) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs (some id)
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
      ({ skb with room := skb.room - (4 + allowedIpSpace (allowedFamily v4)) },
       { ctx with nextAllowedip := none, allowedipsSeq := 0 },
       .complete { publicKey := pubkey, attrs := attrs ++ [("allowed_ips", Json.arr #[allowedJson v4 addr cidr])] })⌝⦄ := by
  have hn := readInsertedNode v4 addr cidr pid parent (fun k => k.wg = some d)
  have ha := getAllowedips_inserted v4 addr cidr { skb with room := skb.room - 4 }
    (by dsimp; omega) (fun k => k.wg = some d)
  have hb := branch_state_returns (fun k => k.wg = some d)
  have hg : ⦃fun w => ⌜w.k.wg = some d⌝⦄ getNode id
      ⦃⇓ n w => ⌜w.k.wg = some d ∧ n = { newNode addr cidr (allowedBits v4) (some pid) with parent }⌝⦄ := by
    mvcgen [getNode, getDev, getK, invariant]
    all_goals simp_all
  simp [getPeerDumpAllowedSource, listed, List.forIn_cons, List.forIn_nil,
    NlSkb.put, nlaTotal, show ¬ skb.room < 4 by omega, bind_assoc]
  mvcgen [getDev, getK, invariant, hb, hg]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals subst_vars
  all_goals mvcgen [hn, ha, hb]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [Nat.sub_sub]
  all_goals subst_vars
  all_goals mvcgen [ha, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [Nat.sub_sub]
  all_goals grind only

theorem dumpTail_single (v4 : Bool) (d : Device) (p : Peer) (id : NodeId)
    (pid : PeerId) (addr cidr : Nat) (parent : Slot) (ctx : DumpCtx) (skb : NlSkb)
    (listed : p.allowedipsList = [id])
    (node : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) (some pid) with parent })
    (fresh : ctx.nextAllowedip = none)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 172 + allowedIpSpace (allowedFamily v4) ≤ skb.room) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
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
  have ha := fun out pubkey attrs bound => dumpAllowed_single v4 d p id pid addr cidr parent
    ctx skb out pubkey attrs listed node sequence bound
  have hb := branch_state_returns (fun k => k.wg = some d)
  simp only [getPeerDumpTailSource, fresh, listed, List.head?_cons]
  simp [NlSkb.put, nlaTotal, Nat.sub_sub,
    r4, r40, r76, r96, r104, r116, r128, r136, r156, r168]
  mvcgen [hb, ha]
  all_goals clear hb ha
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerFixedSpace, peerFixedAttrs, NlSkb.put, nlaTotal, Nat.sub_sub]
  all_goals try omega
  all_goals cases he : p.endpoint <;> simp_all [NlSkb.put, Nat.sub_sub, Nat.add_assoc]
  all_goals omega

theorem getPeerDump_single (v4 : Bool) (d : Device) (p : Peer) (id : NodeId)
    (pid : PeerId) (addr cidr : Nat) (parent : Slot) (ctx : DumpCtx) (skb : NlSkb)
    (resident : d.peers[pid]? = some p) (listed : p.allowedipsList = [id])
    (node : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) (some pid) with parent })
    (fresh : ctx.nextAllowedip = none)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq)
    (room : 172 + allowedIpSpace (allowedFamily v4) ≤ skb.room) :
    Returns (getPeerDump pid ctx skb) (fun w => w.k.wg = some d)
      (fun result w => w.k.wg = some d ∧ result =
        ({ skb with room := skb.room - (peerFixedSpace p + 4 + allowedIpSpace (allowedFamily v4)) },
         { ctx with nextAllowedip := none, allowedipsSeq := 0 },
         .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs p ++ [("allowed_ips", Json.arr #[allowedJson v4 addr cidr])] })) := by
  have hg : Returns (getPeer pid) (fun w => w.k.wg = some d)
      (fun q w => q = p ∧ w.k.wg = some d) := by
    rw [returns_iff]
    mvcgen [getPeer, getDev, getK, invariant]
    all_goals simp_all
  rw [getPeerDump_source]
  apply returns_bind _ _ hg
  intro q w h
  obtain ⟨same, hd⟩ := h
  subst q
  exact (returns_iff _ _ _).mpr
    (dumpTail_single v4 d p id pid addr cidr parent ctx skb listed node fresh sequence room) w hd

end Leanux.Proofs.WG.Config
