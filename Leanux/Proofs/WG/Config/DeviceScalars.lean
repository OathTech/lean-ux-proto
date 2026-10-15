import Leanux.Proofs.WG.Config.ScalarReturns
import Leanux.Proofs.WG.Config.DeviceSource
import Leanux.Proofs.WG.Config.DumpReturns

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def byIndex (d : Device) : DeviceRef :=
  { ifname := none, ifindex := some d.ifindex }

def selectsDevice (w : World) (d : Device) : Prop :=
  (w.fixtureNetDevices ++ [(d.ifname, d.ifindex, some "wireguard")]).find?
    (fun r => some r.2.1 == some d.ifindex) =
      some (d.ifname, d.ifindex, some "wireguard")

theorem lookupInterface_index (d : Device) :
    ⦃fun w => ⌜w.k.wg = some d ∧ selectsDevice w d⌝⦄ lookupInterface (byIndex d)
    ⦃⇓ ret w => ⌜ret = .ok () ∧ w.k.wg = some d⌝⦄ := by
  mvcgen [lookupInterface, byIndex, netDevices, getK, branch, Leanux.WG.orM, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [selectsDevice, -List.find?_eq_none]
  all_goals grind only

def partialAttrs (d : Device) (key psk : Key) (interval : Nat) : DeviceAttrs :=
  { device := byIndex d, peers := some [.attrs (scalarAttrs key psk interval), .malformed] }

theorem devicePeers_partial (selector d : Device) (key psk : Key) (interval : Nat)
    (pid : PeerId) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ devicePeersSource (partialAttrs selector key psk interval)
    ⦃⇓ ret w => ⌜ret = -EINVAL ∧ w.k.wg = some (scalarDevice d pid p psk interval)⌝⦄ := by
  have hs := (returns_iff _ _ _).mp
    (setPeer_scalars_down_returns key psk interval pid d p found resident live bounded down)
  simp [devicePeersSource, partialAttrs]
  mvcgen [branch, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

theorem setDevice_partial (d : Device) (key psk : Key) (interval : Nat)
    (pid : PeerId) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Returns (wgSetDevice (partialAttrs d key psk interval))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = -EINVAL ∧ w.k.wg = some
        (scalarDevice { d with deviceUpdateGen := d.deviceUpdateGen + 1 } pid p psk interval)) := by
  let updated := { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
  have hl := lookupInterface_index d
  have hp := devicePeers_partial d updated key psk interval pid p found resident live bounded down
  rw [← wgSetDevice_source, returns_iff]
  simp only [wgSetDeviceSource, deviceUpdateSource, deviceKeySource, partialAttrs]
  mvcgen [Leanux.WG.orM, Leanux.WG.andM, branch, modifyDev, modifyK, invariant, hl, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [updated, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS]
  all_goals first | exact hp _ (by simp_all [updated]) | grind only

theorem partial_get_after_set (d : Device) (key psk : Key) (interval : Nat)
    (pid : PeerId) (p : Peer) (ctx : DumpCtx) (skb : NlSkb)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = [])
    (room : 168 ≤ skb.room) :
    Returns (do
      let ret ← wgSetDevice (partialAttrs d key psk interval)
      let dump ← getPeerDump pid ctx skb
      pure (ret, dump))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun result w =>
        let updated := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        peerAt w pid = some updated ∧ result =
          (-EINVAL, { skb with room := skb.room - peerFixedSpace updated },
           { ctx with nextAllowedip := none, allowedipsSeq := 0 },
           .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs updated })) := by
  let updated := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
  have hs := (returns_iff _ _ _).mp
    (setDevice_partial d key psk interval pid p found resident live bounded down)
  have hd := (returns_iff _ _ _).mp (getPeerDump_no_allowedips_returns pid updated ctx skb fresh
    (by simpa [updated] using empty) room)
  rw [returns_iff]
  mvcgen [hs, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerAt, updated, scalarDevice, withPeer]

end Leanux.Proofs.WG.Config
