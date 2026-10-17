import Leanux.Proofs.WG.Config.PeerScalars
import Leanux.Proofs.WG.Config.PeerDump

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem scalars_get_after_set (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer) (ctx : DumpCtx) (skb : NlSkb)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (down : d.running = false)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = [])
    (room : 168 ≤ skb.room) :
    Ensures (do
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
  refine ensures_bind _ _ (setPeer_scalars_down key psk interval pid d p found resident live down) ?_
  intro ret
  refine ensures_bind (Q := fun dump w => ret = 0 ∧ peerAt w pid = some updated ∧
    dump = ({ skb with room := skb.room - peerFixedSpace updated },
      { ctx with nextAllowedip := none, allowedipsSeq := 0 },
      .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs updated })) _ _ ?_ ?_
  · intro g ambient dump final after pre run
    obtain ⟨rfl, device⟩ := pre
    have peer : peerAt g pid = some updated := by
      simp [peerAt, device, scalarDevice_peer, updated]
    have result := getPeerDump_no_allowedips pid updated ctx skb fresh
      (by simpa [updated] using empty) room g ambient dump final after peer run
    exact ⟨rfl, result⟩
  · intro dump g ambient result final after pre run
    simp at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    rcases pre with ⟨rfl, peer, rfl⟩
    exact ⟨peer, rfl⟩

end Leanux.Proofs.WG.Config
