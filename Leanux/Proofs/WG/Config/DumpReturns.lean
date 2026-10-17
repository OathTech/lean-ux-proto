import Leanux.Proofs.WG.Config.OperationFrames
import Leanux.Proofs.WG.Config.PeerDump
import Leanux.Proofs.WG.Config.Returns

set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem dumpAllowed_none_returns (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json)) (P : WGWorld → Prop) :
    ⦃fun w => ⌜P w⌝⦄ getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs none
    ⦃⇓ result w => ⌜P w ∧ result =
      (skb, { ctx with nextAllowedip := none, allowedipsSeq := 0 },
        .complete { publicKey := pubkey, attrs })⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient hp
  exact ⟨_, g, _, rfl, hp, rfl⟩

theorem dumpTail_no_allowedips_returns (p : Peer) (ctx : DumpCtx) (skb : NlSkb)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = [])
    (room : 168 ≤ skb.room) (P : WGWorld → Prop) :
    ⦃fun w => ⌜P w⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓ result w => ⌜P w ∧ result =
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
  apply (returns_iff _ _ _).mp
  intro g ambient hp
  cases run : ((getPeerDumpTailSource p ctx skb).run g).run ambient with
  | error error =>
    have different : AF_INET6 ≠ AF_INET := by decide
    by_cases v4 : (p.endpoint.map (·.family)).getD 0 = AF_INET <;>
      by_cases v6 : (p.endpoint.map (·.family)).getD 0 = AF_INET6
    all_goals
      simp [getPeerDumpTailSource, getPeerDumpAllowedSource, fresh, empty,
        branch, AmbientM.branch, NlSkb.put, nlaTotal, Nat.sub_sub,
        r4, r40, r76, r96, r104, r116, r128, r136, r156, r168,
        v4, v6, different] at run
      cases run
  | ok out =>
    rcases out with ⟨⟨result, final⟩, after⟩
    exact ⟨result, final, after, rfl,
      (ensures_iff _ _ _).mpr (dumpTail_no_allowedips p ctx skb fresh empty room P)
        g ambient result final after hp run⟩

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
    apply (returns_iff _ _ _).mp
    intro g ambient hp
    cases hd : g.dev with
    | none => simp [peerAt, hd] at hp
    | some d =>
      have resident : d.peers[pid]? = some p := by simpa [peerAt, hd] using hp
      refine ⟨p, g, ambient, ?_, rfl, hp⟩
      simp [getPeer, getDev, hd, resident]
      rfl
  rw [getPeerDump_source]
  apply returns_bind
  · exact (returns_iff _ _ _).mpr hg
  · intro q w ambient h
    rcases h with ⟨hqp, hp⟩
    subst q
    exact (returns_iff _ _ _).mpr
      (dumpTail_no_allowedips_returns p ctx skb fresh empty room
        (fun g => peerAt g pid = some p)) w ambient hp

end Leanux.Proofs.WG.Config
