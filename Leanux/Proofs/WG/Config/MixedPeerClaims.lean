import Leanux.Proofs.WG.Config.MixedPeerFrames
import Leanux.Proofs.WG.Config.MixedPeerSource
import Leanux.Proofs.WG.Config.AllowedRoundTripSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do Lean

/-- Actual set/readback for a resident peer on a stopped device. Allocation refusal and a
malformed second Allowed-IP retain earlier writes; only full success reaches
the keepalive assignment. The JSON uses the mirror's exact address masking. -/
theorem mixed_peer_allowedip_get_after_set (v4 : Bool) (key psk : Key)
    (interval addr cidr : Nat) (bad : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (ctx : DumpCtx) (skb : NlSkb)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (empty : p.allowedipsList = []) (root : allowedRootValue v4 d = none)
    (width : cidr ≤ allowedBits v4) (fresh : ctx.nextAllowedip = none)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq + 1)
    (room : 172 + allowedIpSpace (allowedFamily v4) ≤ skb.room) :
    Campaign2.Ensures (do
      let ret ← setPeerCmd (mixedPeerAttrs v4 key psk interval addr cidr bad)
      let dump ← getPeerDump pid ctx skb
      pure (ret, dump))
      (fun s => s.wg.device = some d)
      (fun result s => ∃ inserted final,
        s.wg.device = some final ∧
        MixedPeerEffect v4 d pid p psk interval addr cidr bad result.1 final ∧
        result.1 = (if inserted then (if bad then -EINVAL else 0) else -ENOMEM) ∧
        result.2 =
          ({skb with room := skb.room - (peerFixedSpace p +
              (if inserted then 4 + allowedIpSpace (allowedFamily v4) else 0))},
           {ctx with nextAllowedip := none, allowedipsSeq := 0},
           .complete {
             publicKey := hexKey p.remoteStatic
             attrs := peerFixedAttrs (mixedPeerReadback p psk interval d.nextNode bad inserted) ++
               (if inserted then [("allowed_ips", Json.arr #[allowedJson v4 addr cidr])] else [])})) := by
  intro g ambient result final after device run
  change (((setPeerCmd (mixedPeerAttrs v4 key psk interval addr cidr bad)).run g).run ambient >>=
    fun ((ret, middle), next) => ((getPeerDump pid ctx skb).run middle).run next >>=
      fun ((dump, out), rest) => Except.ok (((ret, dump), out), rest)) = _ at run
  cases hs : ((setPeerCmd (mixedPeerAttrs v4 key psk interval addr cidr bad)).run g).run ambient with
  | error stop => rw [hs] at run; cases run
  | ok output =>
    obtain ⟨⟨ret, middle⟩, next⟩ := output
    obtain ⟨current, hd, effect⟩ := setPeer_mixed_allowedip v4 key psk interval addr cidr bad
      d pid p found resident live bounded down root width g ambient ret middle next device hs
    obtain ⟨inserted, code, selected, node, seq⟩ :=
      mixedPeerEffect_readback v4 d pid p psk interval addr cidr bad ret current effect
    rw [hs] at run
    change (((getPeerDump pid ctx skb).run middle).run next >>=
      fun ((dump, out), rest) => Except.ok (((ret, dump), out), rest)) = _ at run
    cases inserted with
    | false =>
      obtain ⟨dump, out, rest, hg, same, value⟩ := getPeerDump_empty_device current pid
        (mixedPeerReadback p psk interval d.nextNode bad false) ctx skb selected
        (by simpa [mixedPeerReadback] using empty) fresh (by omega) middle next hd
      rw [hg] at run
      cases run
      refine ⟨false, current, same, effect, code, ?_⟩
      simpa [mixedPeerReadback, peerFixedSpace] using value
    | true =>
      obtain ⟨dump, out, rest, hg, same, value⟩ := getPeerDump_single v4 current
        (mixedPeerReadback p psk interval d.nextNode bad true) d.nextNode pid addr cidr
        (allowedRoot v4) ctx skb selected (by simp [mixedPeerReadback, empty]) (node rfl)
        fresh (by simpa [seq] using sequence) room middle next hd
      rw [hg] at run
      cases run
      refine ⟨true, current, same, effect, code, ?_⟩
      simpa [mixedPeerReadback, peerFixedSpace, Nat.add_assoc] using value

end Leanux.Proofs.WG.Config
