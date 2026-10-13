import Leanux.Proofs.WG.Keypairs.Frames.WGConfig

/-! Receive-state framing for the original WireGuard device lifecycle and transmit paths. -/
namespace Leanux.Proofs.WG.Keypairs.WGDevice
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs
open KernelFrames WGFrames WGTransitions WGMore WGConfig

set_option maxHeartbeats 400000

theorem lookupDst_sameSnapshot (family addr : Nat) : SameSnapshot (lookupDst family addr) := by
  frame_same [lookupDst] using [getDev_spec, lookup_spec]

theorem lookupDst_spec (P : Snapshot → Prop) (family addr : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (lookupDst family addr)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (lookupDst_sameSnapshot family addr).wp P

theorem wgOpen_ordinary  : OrdinaryAction wgOpen := by
  frame_ordinary [wgOpen] using [getDev_spec, socketInit_spec, getPeer_spec] ordinary [sendStagedPackets_spec, sendKeepalive_spec]

theorem wgOpen_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgOpen
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgOpen_ordinary ).wp P hp

theorem wgUp_ordinary  : OrdinaryAction wgUp := by
  frame_ordinary [wgUp] using [] ordinary [wgOpen_spec]

theorem wgUp_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgUp
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgUp_ordinary ).wp P hp

theorem wgStop_ordinary  : OrdinaryAction wgStop := by
  frame_ordinary [wgStop] using [getDev_spec, requireNotPending_spec, purgeStagedPackets_spec, handshakeClear_spec, resetLastSentHandshake_spec, socketReinit_spec] ordinary [timersStop_spec, keypairsClear_spec]

theorem wgStop_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgStop
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgStop_ordinary ).wp P hp

theorem wgDown_ordinary  : OrdinaryAction wgDown := by
  frame_ordinary [wgDown] using [] ordinary [wgStop_spec]

theorem wgDown_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgDown
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgDown_ordinary ).wp P hp

theorem ratelimiterInit_sameSnapshot  : SameSnapshot ratelimiterInit := by
  frame_same [ratelimiterInit] using [envOk_spec, hidden_snapshot_spec]

theorem ratelimiterInit_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ ratelimiterInit
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ratelimiterInit_sameSnapshot ).wp P

theorem gcEntries_sameSnapshot (work : Bool) : SameSnapshot (gcEntries work) := by
  frame_same [gcEntries] using [hiddenClock_spec]

theorem gcEntries_spec (P : Snapshot → Prop) (work : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (gcEntries work)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (gcEntries_sameSnapshot work).wp P

theorem ratelimiterUninit_sameSnapshot  : SameSnapshot ratelimiterUninit := by
  frame_same [ratelimiterUninit] using [gcEntries_spec, mayHaveSlept_spec, skipCut_spec]

theorem ratelimiterUninit_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ ratelimiterUninit
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ratelimiterUninit_sameSnapshot ).wp P

theorem cookieCheckerInit_sameSnapshot  : SameSnapshot cookieCheckerInit := by
  frame_same [cookieCheckerInit] using [hiddenClock_spec, hidden_snapshot_spec]

theorem cookieCheckerInit_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ cookieCheckerInit
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (cookieCheckerInit_sameSnapshot ).wp P

theorem pubkeyHashtableAlloc_sameSnapshot  : SameSnapshot pubkeyHashtableAlloc := by
  frame_same [pubkeyHashtableAlloc] using [envOk_spec, hidden_snapshot_spec]

theorem pubkeyHashtableAlloc_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ pubkeyHashtableAlloc
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pubkeyHashtableAlloc_sameSnapshot ).wp P

theorem wgNewlink_sameSnapshot  : SameSnapshot wgNewlink := by
  frame_same [wgNewlink] using [cookieCheckerInit_spec, pubkeyHashtableAlloc_spec, ratelimiterInit_spec, envOk_spec, mayHaveSlept_spec, skipCutExactly_spec, skipCut_spec]

theorem wgNewlink_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgNewlink
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgNewlink_sameSnapshot ).wp P

theorem clearDevice_ordinary :
    OrdinaryAction (modifyK fun k => { k with wg := none }) := by
  unfold modifyK
  apply ordinary_modify
  intro w
  exact Ordinary.empty (snapshot w)

theorem clearDevice_spec (P : Snapshot → Prop) (hp : Stable P) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (modifyK fun k => { k with wg := none })
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := clearDevice_ordinary.wp P hp

theorem wgSetup_ordinary : OrdinaryAction wgSetup := by
  unfold wgSetup modifyK
  apply ordinary_modify
  intro w
  simpa [snapshot, Snapshot.empty] using Ordinary.empty (snapshot w)

theorem wgSetup_spec (P : Snapshot → Prop) (hp : Stable P) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgSetup
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := wgSetup_ordinary.wp P hp

theorem wgCreate_ordinary  : OrdinaryAction wgCreate := by
  unfold wgCreate
  repeat' first
    | (ordinary_head Leanux.modifyK; exact clearDevice_ordinary)
    | (ordinary_head Leanux.WG.wgSetup; with_reducible exact @wgSetup_ordinary)
    | (ordinary_head Leanux.WG.wgNewlink; refine SameSnapshot.ordinary ?_; with_reducible exact @wgNewlink_sameSnapshot)
    | (ordinary_head Leanux.branch; refine SameSnapshot.ordinary ?_; with_reducible exact @branch_sameSnapshot _ _)
    | (ordinary_head Leanux.branchCmp; refine SameSnapshot.ordinary ?_; with_reducible exact @branchCmp_sameSnapshot _ _ _ _)
    | (ordinary_head Leanux.branchCmpExcluded; refine SameSnapshot.ordinary ?_; with_reducible exact @branchCmpExcluded_sameSnapshot _ _ _)
    | (ordinary_head Leanux.invariant; refine SameSnapshot.ordinary ?_; with_reducible exact @invariant_sameSnapshot _ _)
    | (ordinary_head Leanux.unsupported; refine SameSnapshot.ordinary ?_; with_reducible exact @unsupported_sameSnapshot _ _)
    | (ordinary_head Leanux.getK; unfold Leanux.getK)
    | ordinary_strict_step

theorem wgCreate_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgCreate
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgCreate_ordinary ).wp P hp

theorem wgDestruct_ordinary  : OrdinaryAction wgDestruct := by
  unfold wgDestruct
  repeat' first
    | (ordinary_head Leanux.retireDeviceUnits; unfold Leanux.retireDeviceUnits)
    | (ordinary_head Leanux.modifyK; exact clearDevice_ordinary)
    | (ordinary_head Leanux.WG.peerRemoveAll; with_reducible exact @peerRemoveAll_ordinary)
    | (ordinary_head Leanux.WG.socketReinit; refine SameSnapshot.ordinary ?_; with_reducible exact @socketReinit_sameSnapshot _ _)
    | (ordinary_head Leanux.WG.getDev; refine SameSnapshot.ordinary ?_; with_reducible exact @getDev_sameSnapshot)
    | (ordinary_head Leanux.WG.mayHaveSlept; refine SameSnapshot.ordinary ?_; with_reducible exact @mayHaveSlept_sameSnapshot)
    | (ordinary_head Leanux.WG.ratelimiterUninit; refine SameSnapshot.ordinary ?_; with_reducible exact @ratelimiterUninit_sameSnapshot)
    | (ordinary_head Leanux.branch; refine SameSnapshot.ordinary ?_; with_reducible exact @branch_sameSnapshot _ _)
    | (ordinary_head Leanux.branchCmp; refine SameSnapshot.ordinary ?_; with_reducible exact @branchCmp_sameSnapshot _ _ _ _)
    | (ordinary_head Leanux.branchCmpExcluded; refine SameSnapshot.ordinary ?_; with_reducible exact @branchCmpExcluded_sameSnapshot _ _ _)
    | (ordinary_head Leanux.invariant; refine SameSnapshot.ordinary ?_; with_reducible exact @invariant_sameSnapshot _ _)
    | (ordinary_head Leanux.unsupported; refine SameSnapshot.ordinary ?_; with_reducible exact @unsupported_sameSnapshot _ _)
    | (ordinary_head Leanux.getK; unfold Leanux.getK)
    | ordinary_strict_step

theorem wgDestruct_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgDestruct
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgDestruct_ordinary ).wp P hp

theorem wgDelete_ordinary  : OrdinaryAction wgDelete := by
  frame_ordinary [wgDelete] using [getDev_spec, skipCut_spec, mayHaveSlept_spec] ordinary [wgDown_spec, wgDestruct_spec]

theorem wgDelete_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgDelete
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgDelete_ordinary ).wp P hp

theorem wgXmit_ordinary (family addr : Nat) (pkts : List Packet) (mtu : Nat) : OrdinaryAction (wgXmit family addr pkts mtu) := by
  unfold wgXmit
  repeat' first
    | (ordinary_head Leanux.WG.sendStagedPackets; with_reducible exact @sendStagedPackets_ordinary _)
    | (ordinary_head Leanux.WG.lookupDst; refine SameSnapshot.ordinary ?_; with_reducible exact @lookupDst_sameSnapshot _ _)
    | (ordinary_head Leanux.WG.getPeer; refine SameSnapshot.ordinary ?_; with_reducible exact @getPeer_sameSnapshot _)
    | (ordinary_head Leanux.WG.setPeer; refine SameSnapshot.ordinary ?_; with_reducible exact @setPeer_sameSnapshot _ _)
    | (ordinary_head Leanux.WG.peerPut; refine SameSnapshot.ordinary ?_; with_reducible exact @peerPut_sameSnapshot _)
    | (ordinary_head Leanux.envOk; refine SameSnapshot.ordinary ?_; with_reducible exact @envOk_sameSnapshot _)
    | (ordinary_head Leanux.skipCutSites; refine SameSnapshot.ordinary ?_; with_reducible exact @skipCutSites_sameSnapshot _)
    | (ordinary_head Leanux.WG.loopbackSend; refine SameSnapshot.ordinary ?_; with_reducible exact @loopbackSend_sameSnapshot _ _)
    | (ordinary_head Leanux.branch; refine SameSnapshot.ordinary ?_; with_reducible exact @branch_sameSnapshot _ _)
    | (ordinary_head Leanux.branchCmp; refine SameSnapshot.ordinary ?_; with_reducible exact @branchCmp_sameSnapshot _ _ _ _)
    | (ordinary_head Leanux.branchCmpExcluded; refine SameSnapshot.ordinary ?_; with_reducible exact @branchCmpExcluded_sameSnapshot _ _ _)
    | (ordinary_head Leanux.invariant; refine SameSnapshot.ordinary ?_; with_reducible exact @invariant_sameSnapshot _ _)
    | (ordinary_head Leanux.unsupported; refine SameSnapshot.ordinary ?_; with_reducible exact @unsupported_sameSnapshot _ _)
    | (ordinary_head Leanux.getK; unfold Leanux.getK)
    | ordinary_strict_step

theorem wgXmit_spec (P : Snapshot → Prop) (hp : Stable P) (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (wgXmit family addr pkts mtu)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgXmit_ordinary family addr pkts mtu).wp P hp

theorem setMtu_sameSnapshot (mtu : Nat) : SameSnapshot (setMtu mtu) := by
  frame_same [setMtu] using []

theorem setMtu_spec (P : Snapshot → Prop) (mtu : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (setMtu mtu)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setMtu_sameSnapshot mtu).wp P

theorem netnsPreExit_sameSnapshot  : SameSnapshot netnsPreExit := by
  frame_same [netnsPreExit] using [getDev_spec, socketReinit_spec, clearPeerEndpointSrc_spec]

theorem netnsPreExit_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ netnsPreExit
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (netnsPreExit_sameSnapshot ).wp P

end Leanux.Proofs.WG.Keypairs.WGDevice
