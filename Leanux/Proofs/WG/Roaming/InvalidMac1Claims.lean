import Leanux.Proofs.WG.Roaming.InvalidMac1Frames
import Leanux.Proofs.WG.Roaming.InvalidMac1Source
import Leanux.Proofs.WG.Roaming.View
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

/-- An invalid MAC1 leaves every remote endpoint unchanged on normal completion
of the complete non-cookie receive call. Load/decay clocks remain unrestricted:
this does not assert completion or an endpoint state after a Stop. -/
theorem receiveHandshakePacket_invalid_mac1 (msg : List UInt8) (src : SkbSource)
    (before : Campaign2.Snapshot)
    (noncookie : messageType msg ≠ MESSAGE_HANDSHAKE_COOKIE)
    (invalid : ∀ d, before.wg.device = some d →
      blake2s 16 d.mac1Key (msg.take (msg.length - 32)) ≠
        (msg.drop (msg.length - 32)).take 16) :
    Campaign2.Ensures (receiveHandshakePacket msg src) (fun s => s = before)
      (fun _ after => after.wg.device = before.wg.device ∧
        ∀ pid, remoteAt after pid = remoteAt before pid) := by
  have body : Ensures (Index.receiveLoadThen (Index.receivePacketBody msg src))
      (fun g => g.dev = before.wg.device) (fun _ g => g.dev = before.wg.device) := by
    rw [← responseLoad_source]
    refine ensures_bind _ _ (responseLoad_device before.wg.device) ?_
    intro underLoad g ambient result final after device run
    cases present : g.dev with
    | none =>
      cases underLoad <;>
        simp [Index.receivePacketBody, cookieValidatePacket, getDev, present,
          invariant, AmbientM.invariant] at run
      all_goals cases run
    | some d =>
      have bad := invalid d (device.symm.trans present)
      exact (receivePacketBody_invalid_mac1 msg src underLoad d bad
        g ambient result final after present run).trans (present.symm.trans device)
  intro g ambient result final after pre run
  have device : g.dev = before.wg.device := congrArg (fun s => s.wg.device) pre
  rw [← Index.receivePacket_source] at run
  simp [Index.receivePacketSource, noncookie, branch, AmbientM.branch] at run
  have retained := body _ _ result final after device run
  refine ⟨retained, ?_⟩
  intro pid
  have observed : (Campaign2.snapshot final after).wg.device = before.wg.device := retained
  simp only [remoteAt, Campaign2.Snapshot.peerAt, observed]

end Leanux.Proofs.WG.Roaming
