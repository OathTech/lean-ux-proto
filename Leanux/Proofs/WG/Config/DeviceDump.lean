import Leanux.Proofs.WG.Config.DeviceDumpSource
import Leanux.Proofs.WG.Config.KeyReferences

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

def deviceFixedAttrs (d : Device) : List (String × Json) :=
  [("listen_port", toJson d.incomingPort), ("fwmark", toJson d.fwmark),
    ("ifindex", toJson d.ifindex), ("ifname", toJson d.ifname)] ++
  if d.staticIdentity.hasIdentity then
    [("private_key", toJson (hexKey d.staticIdentity.staticPrivate)),
      ("public_key", toJson (hexKey d.staticIdentity.staticPublic))]
  else []

def devicePrefixSpace (d : Device) : Nat :=
  48 + nlaTotal (d.ifname.length + 1) + if d.staticIdentity.hasIdentity then 72 else 0

def singlePeerDump (d : Device) (p : Peer) : DumpCall :=
  { ret := 0
    skb := { room := NLMSG_GOODSIZE - devicePrefixSpace d - peerFixedSpace p
             messages := [.data 2 (deviceFixedAttrs d)
               (some [{ publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs p }])] }
    ctx := { hasWg := true }
    prevSeq := d.deviceUpdateGen }

theorem getPeerDump_device_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (ctx : DumpCtx) (skb : NlSkb)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = []) (room : 168 ≤ skb.room) :
    Returns (getPeerDump pid ctx skb) (fun w => w.k.wg = some d)
      (fun result w => w.k.wg = some d ∧ result =
        ({ skb with room := skb.room - peerFixedSpace p },
         { ctx with nextAllowedip := none, allowedipsSeq := 0 },
         .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs p })) := by
  have hg : ⦃fun w => ⌜w.k.wg = some d⌝⦄ getPeer pid
      ⦃⇓ q w => ⌜q = p ∧ w.k.wg = some d⌝⦄ := by
    mvcgen [getPeer, getDev, getK, invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals repeat intro
    all_goals simp_all
  rw [getPeerDump_source]
  apply returns_bind
  · exact (returns_iff _ _ _).mpr hg
  · intro q w h
    obtain ⟨heq, hd⟩ := h
    subst q
    exact (returns_iff _ _ _).mpr
      (dumpTail_no_allowedips_returns p ctx skb fresh empty room (fun k => k.wg = some d)) w hd

theorem deviceDumpSource_single (pid : PeerId) (d : Device) (p : Peer)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (empty : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE) :
    Returns (deviceDumpSource d { hasWg := true } 0 {}) (fun w => w.k.wg = some d)
      (fun result w => result = singlePeerDump d p ∧ w.k.wg = some d) := by
  have hp (skb : NlSkb) :
      ⦃fun w => ⌜w.k.wg = some d ∧ 168 ≤ skb.room⌝⦄ getPeerDump pid { hasWg := true } skb
      ⦃⇓ result w => ⌜w.k.wg = some d ∧ result =
        ({ skb with room := skb.room - peerFixedSpace p }, { hasWg := true },
          .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs p })⌝⦄ := by
    intro w ⟨hd, hr⟩
    exact (returns_iff _ _ _).mp
      (getPeerDump_device_returns pid d p resident { hasWg := true } skb rfl empty hr) w hd
  have hput : ⦃fun w => ⌜w.k.wg = some d⌝⦄ peerPut none ⦃⇓ _ w => ⌜w.k.wg = some d⌝⦄ := by
    mvcgen [peerPut, branch]
  have n0 : nlaTotal 0 = 4 := rfl
  have n2 : nlaTotal 2 = 8 := rfl
  have n4 : nlaTotal 4 = 8 := rfl
  have n32 : nlaTotal 32 = 36 := rfl
  have rn : nlaTotal (d.ifname.length + 1) + 236 ≤ 3776 := by
    unfold devicePrefixSpace NLMSG_GOODSIZE at room
    omega
  have rname : ¬ 3732 < nlaTotal (d.ifname.length + 1) := by omega
  have r36 : ¬ 3732 - nlaTotal (d.ifname.length + 1) < 36 := by omega
  have r72 : ¬ 3696 - nlaTotal (d.ifname.length + 1) < 36 := by omega
  have rnest : ¬ 3660 - nlaTotal (d.ifname.length + 1) < 4 := by omega
  have rnest0 : ¬ 3732 - nlaTotal (d.ifname.length + 1) < 4 := by omega
  rw [returns_iff]
  cases identity : d.staticIdentity.hasIdentity
  all_goals simp [deviceDumpSource, peers, identity, branch, WG.orM, WG.andM, bind_assoc,
    NlSkb.put, nlmsgTotal, n0, n2, n4, n32, Nat.sub_sub, rname, r36, r72, rnest, rnest0,
    List.forIn_cons, List.forIn_nil]
  all_goals mvcgen [requireNotPending, unsupported, invariant, hp, hput]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp only [peerPut, branch, bind_assoc]
  all_goals simp_all [NlSkb.put, nlaTotal, nlmsgTotal, NLMSG_GOODSIZE, devicePrefixSpace,
    singlePeerDump, deviceFixedAttrs, Nat.sub_sub, identity]
  all_goals try omega
  all_goals mvcgen [peerPut, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals omega

theorem wgGetDeviceDump_single (pid : PeerId) (d : Device) (p : Peer)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (empty : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE) :
    Returns (wgGetDeviceDump { hasWg := true } 0 {}) (fun w => w.k.wg = some d)
      (fun result w => result = singlePeerDump d p ∧ w.k.wg = some d) := by
  have hg : Returns getDev (fun w => w.k.wg = some d)
      (fun q w => q = d ∧ w.k.wg = some d) := by
    rw [returns_iff]
    mvcgen [getDev, getK, invariant]
    all_goals simp_all
  rw [wgGetDeviceDump_source]
  apply returns_bind _ _ hg
  intro q w h
  obtain ⟨heq, hd⟩ := h
  subst q
  exact deviceDumpSource_single pid d p peers resident empty room w hd

end Leanux.Proofs.WG.Config
