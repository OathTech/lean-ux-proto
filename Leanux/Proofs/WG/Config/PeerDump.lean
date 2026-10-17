import Leanux.Proofs.WG.Config.OperationFrames
import Leanux.Proofs.WG.Config.Validation
import Leanux.Proofs.WG.Config.DumpSource
import Leanux.Proofs.WG.Noise.Slots

set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

def peerFixedAttrs (p : Peer) : List (String × Json) :=
  [("public_key", toJson (hexKey p.remoteStatic)),
   ("preshared_key", toJson (hexKey p.presharedKey)),
   ("last_handshake", toJson (timespec p.walltimeLastHandshake)),
   ("keepalive", toJson p.persistentKeepaliveInterval),
   ("tx_bytes", toJson p.txBytes), ("rx_bytes", toJson p.rxBytes),
   ("protocol_version", toJson 1)] ++
  match p.endpoint with
  | none => []
  | some e =>
    let v4 := e.family == AF_INET
    [("endpoint", Json.mkObj ([("family", toJson (if v4 then 4 else 6)),
      ("addr", toJson (hexBE e.addr (if v4 then 4 else 16))), ("port", toJson e.port)] ++
      (if v4 then [] else [("flowinfo", toJson e.flowinfo), ("scope_id", toJson e.scope)])))]

def peerFixedSpace (p : Peer) : Nat :=
  136 + if (p.endpoint.map (·.family)).getD 0 = AF_INET then 20
        else if (p.endpoint.map (·.family)).getD 0 = AF_INET6 then 32 else 0

theorem dumpAllowed_none (p : Peer) (ctx : DumpCtx) (skb0 skb : NlSkb)
    (pubkey : String) (attrs : List (String × Json)) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ getPeerDumpAllowedSource p ctx skb0 skb pubkey attrs none
    ⦃⇓? result w => ⌜P w.k ∧ result =
      (skb, { ctx with nextAllowedip := none, allowedipsSeq := 0 },
        .complete { publicKey := pubkey, attrs })⌝⦄ := by
  mvcgen [getPeerDumpAllowedSource, branch]

theorem dumpTail_no_allowedips (p : Peer) (ctx : DumpCtx) (skb : NlSkb)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = [])
    (room : 168 ≤ skb.room) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ getPeerDumpTailSource p ctx skb
    ⦃⇓? result w => ⌜P w.k ∧ result =
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
  have ha := fun out pubkey attrs => dumpAllowed_none p ctx skb out pubkey attrs P
  have hb := branch_state_spec P
  simp only [getPeerDumpTailSource, fresh, empty, List.head?_nil]
  simp [NlSkb.put, nlaTotal, Nat.sub_sub,
    r4, r40, r76, r96, r104, r116, r128, r136, r156, r168]
  mvcgen [hb, ha]
  all_goals clear hb ha
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerFixedSpace, peerFixedAttrs, NlSkb.put, nlaTotal, Nat.sub_sub]
  all_goals cases he : p.endpoint <;> simp_all [NlSkb.put, Nat.sub_sub]

theorem getPeerDump_no_allowedips (pid : PeerId) (p : Peer) (ctx : DumpCtx) (skb : NlSkb)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = [])
    (room : 168 ≤ skb.room) :
    Ensures (getPeerDump pid ctx skb) (fun w => peerAt w pid = some p)
      (fun result w => peerAt w pid = some p ∧ result =
        ({ skb with room := skb.room - peerFixedSpace p },
         { ctx with nextAllowedip := none, allowedipsSeq := 0 },
         .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs p })) := by
  rw [getPeerDump_source]
  apply ensures_bind
  · exact (ensures_iff _ _ _).mpr (getPeer_exact_spec pid p)
  · intro q w r v h hr
    rcases h with ⟨hqp, hp⟩
    subst q
    exact (ensures_iff _ _ _).mpr
      (dumpTail_no_allowedips p ctx skb fresh empty room
        (fun k => (k.wg.bind fun d => d.peers[pid]?) = some p)) w r v hp hr

end Leanux.Proofs.WG.Config
