import Leanux.Proofs.WG.Config.PeerDump
import Leanux.Proofs.WG.Config.Returns

set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem branch_kernel_returns (P : Kernel → Prop) (decision : Decision) (outcome : Bool) :
    ⦃fun w => ⌜P w.k⌝⦄ branch decision outcome
    ⦃⇓ ret w => ⌜ret = outcome ∧ P w.k⌝⦄ := by
  mvcgen [branch]

theorem dumpAllowed_none_returns (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json)) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs none
    ⦃⇓ result w => ⌜P w.k ∧ result =
      (skb, { ctx with nextAllowedip := none, allowedipsSeq := 0 },
        .complete { publicKey := pubkey, attrs })⌝⦄ := by
  mvcgen [getPeerDumpAllowedSource, branch]

theorem dumpTail_no_allowedips_returns (p : Peer) (ctx : DumpCtx) (skb : NlSkb)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = [])
    (room : 168 ≤ skb.room) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓ result w => ⌜P w.k ∧ result =
      ({ skb with room := skb.room - peerFixedSpace p },
       { ctx with nextAllowedip := none, allowedipsSeq := 0 },
       .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs p })⌝⦄ := by
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
  have ha := fun out pubkey attrs => dumpAllowed_none_returns p ctx skb out pubkey attrs P
  have hb := branch_kernel_returns P
  simp only [getPeerDumpTailSource, fresh, empty, List.head?_nil]
  simp [NlSkb.put, nlaTotal, Nat.sub_sub,
    r4, r40, r76, r96, r104, r116, r128, r136, r156, r168]
  mvcgen [hb, ha]
  all_goals clear hb ha
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerFixedSpace, peerFixedAttrs, NlSkb.put, nlaTotal, Nat.sub_sub]
  all_goals cases he : p.endpoint <;> simp_all [NlSkb.put, Nat.sub_sub]

theorem getPeerDump_no_allowedips_returns (pid : PeerId) (p : Peer) (ctx : DumpCtx) (skb : NlSkb)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = [])
    (room : 168 ≤ skb.room) :
    Returns (getPeerDump pid ctx skb) (fun w => peerAt w pid = some p)
      (fun result w => peerAt w pid = some p ∧ result =
        ({ skb with room := skb.room - peerFixedSpace p },
         { ctx with nextAllowedip := none, allowedipsSeq := 0 },
         .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs p })) := by
  have hg : ⦃fun w => ⌜peerAt w pid = some p⌝⦄ getPeer pid
      ⦃⇓ q w => ⌜q = p ∧ peerAt w pid = some p⌝⦄ := by
    mvcgen [getPeer, getDev, getK, invariant]
    all_goals simp_all [peerAt]
  rw [getPeerDump_source]
  apply returns_bind
  · exact (returns_iff _ _ _).mpr hg
  · intro q w h
    rcases h with ⟨hqp, hp⟩
    subst q
    exact (returns_iff _ _ _).mpr
      (dumpTail_no_allowedips_returns p ctx skb fresh empty room
        (fun k => (k.wg.bind fun d => d.peers[pid]?) = some p)) w hp

end Leanux.Proofs.WG.Config
