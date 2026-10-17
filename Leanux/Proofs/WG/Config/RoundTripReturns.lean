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
      (fun w => w.dev = some d)
      (fun result w =>
        let updated := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        peerAt w pid = some updated ∧ result =
          (0, { skb with room := skb.room - peerFixedSpace updated },
           { ctx with nextAllowedip := none, allowedipsSeq := 0 },
           .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs updated })) := by
  let updated := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
  refine returns_bind _ _
    (setPeer_scalars_down_returns key psk interval pid d p found resident live bounded down) ?_
  intro ret
  refine returns_bind (Q := fun dump w => ret = 0 ∧ peerAt w pid = some updated ∧
    dump = ({ skb with room := skb.room - peerFixedSpace updated },
      { ctx with nextAllowedip := none, allowedipsSeq := 0 },
      .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs updated })) _ _ ?_ ?_
  · intro g ambient pre
    obtain ⟨rfl, device⟩ := pre
    have peer : peerAt g pid = some updated := by
      simp [peerAt, device, scalarDevice_peer, updated]
    obtain ⟨dump, final, after, run, result⟩ := getPeerDump_no_allowedips_returns pid updated ctx skb fresh
      (by simpa [updated] using empty) room g ambient peer
    exact ⟨dump, final, after, run, rfl, result⟩
  · intro dump g ambient pre
    rcases pre with ⟨rfl, peer, rfl⟩
    exact ⟨_, g, ambient, rfl, peer, rfl⟩

end Leanux.Proofs.WG.Config
