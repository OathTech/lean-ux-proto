import Leanux.Proofs.WG.Noise.PeerFrames
import Leanux.Proofs.WG.Noise.ExpirySource
import Leanux.Proofs.WG.Noise.InitiationSource
import Leanux.Proofs.WG.Noise.ResponseSource

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

theorem beginSession_tag (pid : PeerId) (old : Nat) :
    Ensures (beginSession pid) (fun w => tagAt w.k pid = some old)
      (fun ok w => tagAt w.k pid = some (if ok then HANDSHAKE_ZEROED else old) ∧
        (ok = true → old = HANDSHAKE_CREATED_RESPONSE ∨ old = HANDSHAKE_CONSUMED_RESPONSE)) := by
  rw [ensures_iff]
  have hc := keypairCreate_peers_spec (fun ps => (ps pid).map Peer.handshakeState = some old)
  have hd := deriveKeys_peers_spec (fun ps => (ps pid).map Peer.handshakeState = some old)
  have hi := indexReplaceHandshake_peers_spec (fun ps => (ps pid).map Peer.handshakeState = some 0)
  have ha := fun kp => addNewKeypair_tag_spec pid kp 0
  mvcgen [beginSession, IndexOwner.peerDeref, IndexOwner.peerWord, Leanux.WG.andM, handshakeZero, getPeer, getKeypair,
    getDev, getK, setPeer, setKeypair, modifyDev, modifyK, branch, invariant,
    unsupported, hc, hd, hi, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [tagAt, peerAt, HANDSHAKE_ZEROED, Option.bind_map, Function.comp_def,
    Std.TreeMap.getElem?_insert]
  all_goals try assumption
  all_goals grind (gen := 8)

end Leanux.Proofs.WG.Noise
