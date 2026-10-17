import Leanux.Proofs.WG.Config.ScalarReturns
import Leanux.Proofs.WG.Config.DeviceSource
import Leanux.Proofs.WG.Config.DumpReturns

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def byIndex (d : Device) : DeviceRef :=
  { ifname := none, ifindex := some d.ifindex }

def selectsDevice (w : WGWorld) (d : Device) : Prop :=
  (w.fixtureNetDevices ++ [(d.ifname, d.ifindex, some "wireguard")]).find?
    (fun r => some r.2.1 == some d.ifindex) =
      some (d.ifname, d.ifindex, some "wireguard")

theorem lookupInterface_index (d : Device) :
    ⦃fun w => ⌜w.dev = some d ∧ selectsDevice w d⌝⦄ lookupInterface (byIndex d)
    ⦃⇓ ret w => ⌜ret = .ok () ∧ w.dev = some d⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient pre
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site, outcome := value, netRx := a.netRxSection}}
  let after := mark (mark (mark (mark (mark (mark (mark ambient
    .lookupBothOrNeither false) .lookupHasIfindex true) .lookupNoDev false)
    .lookupNoLinkOps false) .lookupNoKind false) .lookupKindMismatch false) .lookupNotWireguard false
  refine ⟨.ok (), g, after, ?_, rfl, pre.1⟩
  have selected := pre.2
  simp [selectsDevice] at selected
  simp [lookupInterface, byIndex, netDevices, pre.1, selected, WG.orM,
    branch, AmbientM.branch, after, mark]
  rfl

def partialAttrs (d : Device) (key psk : Key) (interval : Nat) : DeviceAttrs :=
  { device := byIndex d, peers := some [.attrs (scalarAttrs key psk interval), .malformed] }

theorem devicePeers_partial (selector d : Device) (key psk : Key) (interval : Nat)
    (pid : PeerId) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ devicePeersSource (partialAttrs selector key psk interval)
    ⦃⇓ ret w => ⌜ret = -EINVAL ∧ w.dev = some (scalarDevice d pid p psk interval)⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient device
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site, outcome := value, netRx := a.netRxSection}}
  let before := mark (mark (mark ambient .setDevHasPeers true) .setDevPeersIter true) .setDevParseErr false
  obtain ⟨ret, final, middle, run, result, changed⟩ :=
    setPeer_scalars_down_returns key psk interval pid d p found resident live bounded down g before device
  subst ret
  let after := mark (mark (mark (mark middle .setDevSetPeerErr false)
    .setDevPeersIter true) .setDevParseErr true) .setDevZeroKey false
  refine ⟨-EINVAL, final, after, ?_, rfl, changed⟩
  simp [devicePeersSource, partialAttrs, branch, AmbientM.branch, List.forIn_cons, List.forIn_nil]
  rw [show ((setPeerCmd (scalarAttrs key psk interval)).run g).run before =
    .ok ((0, final), middle) from run]
  rfl

theorem setDevice_partial (d : Device) (key psk : Key) (interval : Nat)
    (pid : PeerId) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Returns (wgSetDevice (partialAttrs d key psk interval))
      (fun w => w.dev = some d ∧ selectsDevice w d)
      (fun ret w => ret = -EINVAL ∧ w.dev = some
        (scalarDevice { d with deviceUpdateGen := d.deviceUpdateGen + 1 } pid p psk interval)) := by
  let updated := {d with deviceUpdateGen := d.deviceUpdateGen + 1}
  let mark (site : Decision) (value : Bool) : WG.M Unit :=
    monadLift (modify fun a : Ambient => {a with steps := a.steps.push {
      decision := site, outcome := value, netRx := a.netRxSection}} : AmbientM Unit)
  have branchSource (site : Decision) (value : Bool) :
      (branch site value : WG.M Bool) = (do mark site value; pure value) := rfl
  have hm (site : Decision) (value : Bool) (entry : Device) :
      Returns (mark site value) (fun g => g.dev = some entry)
        (fun _ g => g.dev = some entry) := by
    intro g ambient device
    exact ⟨(), g, {ambient with steps := ambient.steps.push {
      decision := site, outcome := value, netRx := ambient.netRxSection}}, rfl, device⟩
  have hu : Returns (modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1})
      (fun g => g.dev = some d) (fun _ g => g.dev = some updated) := by
    intro g ambient device
    refine ⟨(), {g with dev := some updated}, ambient, ?_, rfl⟩
    simp [modifyDev, device, updated]
    rfl
  have tail : Returns (do
      mark .setDevLookupErr false
      mark .setDevHasFlags false
      mark .setDevBadFlags false
      mark .setDevHasPort false
      mark .setDevHasFwmark false
      modifyDev fun d => {d with deviceUpdateGen := d.deviceUpdateGen + 1}
      mark .setDevFwmark false
      mark .setDevPort false
      mark .setDevReplacePeers false
      mark .setDevHasPrivateKey false
      devicePeersSource (partialAttrs d key psk interval))
      (fun g => g.dev = some d)
      (fun ret g => ret = -EINVAL ∧ g.dev = some (scalarDevice updated pid p psk interval)) := by
    refine returns_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ d) (fun _ => ?_)
    refine returns_bind _ _ hu (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ updated) (fun _ => ?_)
    refine returns_bind _ _ (hm _ _ updated) (fun _ => ?_)
    exact (returns_iff _ _ _).mpr
      (devicePeers_partial d updated key psk interval pid p found resident live bounded down)
  rw [← wgSetDevice_source]
  unfold wgSetDeviceSource
  refine returns_bind _ _ ((returns_iff _ _ _).mpr (lookupInterface_index d)) ?_
  intro ret g ambient pre
  obtain ⟨rfl, device⟩ := pre
  simpa [partialAttrs, deviceUpdateSource, deviceKeySource, WG.orM, WG.andM,
    branchSource, bind_assoc, WGDEVICE_F_ALL, WGDEVICE_F_REPLACE_PEERS] using tail g ambient device

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
      (fun w => w.dev = some d ∧ selectsDevice w d)
      (fun result w =>
        let updated := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        peerAt w pid = some updated ∧ result =
          (-EINVAL, { skb with room := skb.room - peerFixedSpace updated },
           { ctx with nextAllowedip := none, allowedipsSeq := 0 },
           .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs updated })) := by
  let updated := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
  refine returns_bind _ _
    (setDevice_partial d key psk interval pid p found resident live bounded down) ?_
  intro ret
  refine returns_bind (Q := fun dump w => ret = -EINVAL ∧ peerAt w pid = some updated ∧
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
