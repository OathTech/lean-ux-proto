import Leanux.Proofs.WG.Config.DeviceDump

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem getPeerDump_device_returns_framed (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (ctx : DumpCtx) (skb : NlSkb)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = []) (room : 168 ≤ skb.room) (P : WGWorld → Prop) :
    Returns (getPeerDump pid ctx skb) (fun w => w.dev = some d ∧ P w)
      (fun result w => (w.dev = some d ∧ P w) ∧ result =
        ({ skb with room := skb.room - peerFixedSpace p },
         { ctx with nextAllowedip := none, allowedipsSeq := 0 },
         .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs p })) := by
  have hg : Returns (getPeer pid) (fun g => g.dev = some d ∧ P g)
      (fun q g => q = p ∧ g.dev = some d ∧ P g) := by
    intro g ambient pre
    obtain ⟨device, framed⟩ := pre
    refine ⟨p, g, ambient, ?_, rfl, device, framed⟩
    simp [getPeer, getDev, device, resident]
    rfl
  rw [getPeerDump_source]
  apply returns_bind
  · exact hg
  · intro q w ambient h
    obtain ⟨heq, hd⟩ := h
    subst q
    exact (returns_iff _ _ _).mpr
      (dumpTail_no_allowedips_returns p ctx skb fresh empty room (fun g => g.dev = some d ∧ P g)) w ambient hd

theorem deviceDumpSource_single_framed (pid : PeerId) (d : Device) (p : Peer)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (empty : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE) (P : WGWorld → Prop) :
    Returns (deviceDumpSource d { hasWg := true } 0 {}) (fun w => w.dev = some d ∧ P w)
      (fun result w => result = singlePeerDump d p ∧ w.dev = some d ∧ P w) := by
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
  intro g ambient pre
  obtain ⟨device, framed⟩ := pre
  let log (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let front := log (log (log (log (log (log (log ambient
    .dumpNoHdr false) .dumpFirst true) .dumpPutPort false) .dumpPutFwmark false)
    .dumpPutIfindex false) .dumpPutIfname false) .dumpHasIdentity d.staticIdentity.hasIdentity
  let withIdentity := if d.staticIdentity.hasIdentity then
    log (log front .dumpPutPrivate false) .dumpPutPublic false else front
  let inputs := log (log (log (log withIdentity .dumpNoPeersNest false)
    .dumpPeerListEmpty false) .dumpCursorSet false) .dumpPeerIter true
  let skb : NlSkb := {room := (if d.staticIdentity.hasIdentity then 3656 - nlaTotal (d.ifname.length + 1) else 3728 - nlaTotal (d.ifname.length + 1))}
  cases identity : d.staticIdentity.hasIdentity
  all_goals simp [deviceDumpSource, peers, identity, branch, AmbientM.branch, WG.orM, WG.andM,
    NlSkb.put, nlmsgTotal, n0, n2, n4, n32, Nat.sub_sub, rname, r36, r72, rnest, rnest0,
    List.forIn_cons, List.forIn_nil, bind_assoc, requireNotPending]
  all_goals
    have sufficient : 168 ≤ skb.room := by
      simp only [skb, identity, Bool.false_eq_true, ite_false, ite_true]
      simp only [devicePrefixSpace, identity, NLMSG_GOODSIZE, Bool.false_eq_true, ite_false, ite_true] at room
      omega
    obtain ⟨out, current, after, run, same, value⟩ :=
      getPeerDump_device_returns_framed pid d p resident {hasWg := true} skb rfl empty sufficient P
        g inputs ⟨device, framed⟩
    subst out
    simp only [skb, inputs, withIdentity, front, log, identity, Bool.false_eq_true, ite_false, ite_true] at run
    rw [run]
    refine ⟨_, current, ⟨_, rfl⟩, ?_, same⟩
    simp [singlePeerDump, deviceFixedAttrs, devicePrefixSpace, identity,
      NLMSG_GOODSIZE, Nat.sub_sub]
    omega

theorem wgGetDeviceDump_single_framed (pid : PeerId) (d : Device) (p : Peer)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (empty : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE) (P : WGWorld → Prop) :
    Returns (wgGetDeviceDump { hasWg := true } 0 {}) (fun w => w.dev = some d ∧ P w)
      (fun result w => result = singlePeerDump d p ∧ w.dev = some d ∧ P w) := by
  have hg : Returns getDev (fun g => g.dev = some d ∧ P g)
      (fun q g => q = d ∧ g.dev = some d ∧ P g) := by
    intro g ambient pre
    obtain ⟨device, framed⟩ := pre
    refine ⟨d, g, ambient, ?_, rfl, device, framed⟩
    simp [getDev, device]
    rfl
  rw [wgGetDeviceDump_source]
  apply returns_bind _ _ hg
  intro q w ambient h
  obtain ⟨heq, hd⟩ := h
  subst q
  exact deviceDumpSource_single_framed pid d p peers resident empty room P w ambient hd

end Leanux.Proofs.WG.Config
