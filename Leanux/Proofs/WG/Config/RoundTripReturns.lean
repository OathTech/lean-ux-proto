import Leanux.Proofs.WG.Config.ScalarReturns
import Leanux.Proofs.WG.Config.DumpReturns

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem scalars_get_after_set_returns (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer) (ctx : DumpCtx) (skb : NlSkb)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = [])
    (room : 168 ≤ skb.room) :
    Returns (do
      let ret ← setPeerCmd (scalarAttrs key psk interval)
      let dump ← getPeerDump pid ctx skb
      pure (ret, dump))
      (fun w => w.k.wg = some d)
      (fun result w =>
        let updated := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        peerAt w pid = some updated ∧ result =
          (0, { skb with room := skb.room - peerFixedSpace updated },
           { ctx with nextAllowedip := none, allowedipsSeq := 0 },
           .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs updated })) := by
  let updated := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
  have hs := (returns_iff _ _ _).mp (setPeer_scalars_down_returns key psk interval pid d p found resident live bounded down)
  have hd := (returns_iff _ _ _).mp (getPeerDump_no_allowedips_returns pid updated ctx skb fresh
    (by simpa [updated] using empty) room)
  rw [returns_iff]
  mvcgen [hs, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerAt, updated, scalarDevice, withPeer]

end Leanux.Proofs.WG.Config
