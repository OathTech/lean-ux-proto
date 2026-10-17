import Leanux.Proofs.Framing.EnvOperations
import Leanux.Proofs.WG.Keypairs.Frames.WGConfig
import Leanux.Proofs.Framing.WGDeviceLifecycle

/-! Receive-state framing for the original WireGuard device lifecycle and transmit paths. -/
namespace Leanux.Proofs.WG.Keypairs.WGDevice
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Keypairs
open Leanux.Proofs.Framing WGFrames WGTransitions WGMore WGConfig

set_option maxHeartbeats 400000

theorem lookupDst_sameSnapshot (family addr : Nat) : SameSnapshot (lookupDst family addr) := by
  snapshot_source [lookupDst] using [getDev_sameSnapshot, lookup_sameSnapshot]

theorem lookupDst_spec (P : Snapshot → Prop) (family addr : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (lookupDst family addr)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (lookupDst_sameSnapshot family addr).wp P

theorem wgOpen_ordinary  : OrdinaryAction wgOpen := by
  transition_ordinary [wgOpen] using [getDev_sameSnapshot, socketInit_sameSnapshot, getPeer_sameSnapshot, sendStagedPackets_ordinary, sendKeepalive_ordinary]

theorem wgOpen_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgOpen
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgOpen_ordinary ).wp P hp

theorem wgUp_ordinary  : OrdinaryAction wgUp := by
  transition_ordinary [wgUp] using [wgOpen_ordinary]

theorem wgUp_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgUp
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgUp_ordinary ).wp P hp

theorem wgStop_ordinary  : OrdinaryAction wgStop := by
  transition_ordinary [wgStop] using [getDev_sameSnapshot, requireNotPending_sameSnapshot, purgeStagedPackets_sameSnapshot, handshakeClear_sameSnapshot, resetLastSentHandshake_sameSnapshot, socketReinit_sameSnapshot, timersStop_ordinary, keypairsClear_ordinary]

theorem wgStop_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgStop
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgStop_ordinary ).wp P hp

theorem wgDown_ordinary  : OrdinaryAction wgDown := by
  transition_ordinary [wgDown] using [wgStop_ordinary]

theorem wgDown_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgDown
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgDown_ordinary ).wp P hp

theorem sameSnapshot_of_sameLink
    {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun s => Framing.linkView (project s)) a) :
    SameView (fun s => snapshot (project s)) a := by
  apply ha.of_factor snapshotOfWGStoreView (fun s => snapshot (project s))
  intro s
  simp [snapshot, snapshotOfWGStoreView, Framing.linkView, Framing.linkStore,
    Framing.linkDevice, Framing.wgStoreView, Option.bind_map, Function.comp_def]

theorem ratelimiterInit_sameSnapshot  : SameSnapshot ratelimiterInit := by
  exact sameSnapshot_of_sameLink (Framing.ratelimiterInit_sameRatelimiter.of_factor Framing.linkStore Framing.linkView (fun _ => rfl))

theorem ratelimiterInit_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ ratelimiterInit
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ratelimiterInit_sameSnapshot ).wp P

theorem gcEntries_sameSnapshot (work : Bool) : SameSnapshot (gcEntries work) := by
  exact sameSnapshot_of_sameLink ((Framing.gcEntries_sameRatelimiter work).of_factor Framing.linkStore Framing.linkView (fun _ => rfl))

theorem gcEntries_spec (P : Snapshot → Prop) (work : Bool) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (gcEntries work)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (gcEntries_sameSnapshot work).wp P

theorem ratelimiterUninit_sameSnapshot  : SameSnapshot ratelimiterUninit := by
  exact sameSnapshot_of_sameLink (Framing.ratelimiterUninit_sameRatelimiter.of_factor Framing.linkStore Framing.linkView (fun _ => rfl))

theorem ratelimiterUninit_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ ratelimiterUninit
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (ratelimiterUninit_sameSnapshot ).wp P

theorem cookieCheckerInit_sameSnapshot  : SameSnapshot cookieCheckerInit := by
  exact sameSnapshot_of_sameLink Framing.cookieCheckerInit_sameLink

theorem cookieCheckerInit_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ cookieCheckerInit
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (cookieCheckerInit_sameSnapshot ).wp P

theorem pubkeyHashtableAlloc_sameSnapshot  : SameSnapshot pubkeyHashtableAlloc := by
  exact sameSnapshot_of_sameLink Framing.pubkeyHashtableAlloc_sameLink

theorem pubkeyHashtableAlloc_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ pubkeyHashtableAlloc
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (pubkeyHashtableAlloc_sameSnapshot ).wp P

theorem wgNewlink_sameSnapshot : SameSnapshot wgNewlink := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  have he := (Framing.hoare_iff_run_ambient _ _ _).mp
    (Framing.wgNewlink_endpoint (Framing.linkView w)) w ambient x v ambient' rfl hr
  rcases he with ⟨_,he⟩ | ⟨_,he⟩
  all_goals
    have hf := congrArg snapshotOfWGStoreView he
    simpa [snapshot, snapshotOfWGStoreView, Framing.linkView, Framing.linkStore,
      Framing.linkDevice, Framing.wgStoreView, Framing.registeredLink,
      Option.bind_map, Function.comp_def] using hf

theorem wgNewlink_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgNewlink
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgNewlink_sameSnapshot ).wp P

theorem clearDevice_ordinary :
    OrdinaryAction (modify (fun g : WGWorld => { g with dev := none }) : WG.M Unit) := by
  apply ordinary_modify
  intro w
  exact Ordinary.empty (snapshot w)

theorem clearDevice_spec (P : Snapshot → Prop) (hp : Stable P) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (modify (fun g : WGWorld => { g with dev := none }) : WG.M Unit)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := clearDevice_ordinary.wp P hp

theorem wgSetup_ordinary : OrdinaryAction wgSetup := by
  unfold wgSetup
  apply ordinary_modify
  intro w
  simpa [snapshot, Snapshot.empty] using Ordinary.empty (snapshot w)

theorem wgSetup_spec (P : Snapshot → Prop) (hp : Stable P) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgSetup
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := wgSetup_ordinary.wp P hp

theorem wgCreate_ordinary  : OrdinaryAction wgCreate := by
  unfold wgCreate
  repeat' first
    | (ordinary_head modify; exact clearDevice_ordinary)
    | (ordinary_head Leanux.WG.wgSetup; with_reducible exact @wgSetup_ordinary)
    | (ordinary_head Leanux.WG.wgNewlink; refine SameView.ordinary ?_; with_reducible exact @wgNewlink_sameSnapshot)
    | (ordinary_head Leanux.branch; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) (fun s => snapshot s = initial))
    | (ordinary_head Leanux.branchCmp; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.branchCmp _ _ _ _) (fun s => snapshot s = initial))
    | (ordinary_head Leanux.branchCmpExcluded; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.branchCmpExcluded _ _ _) (fun s => snapshot s = initial))
    | (ordinary_head Leanux.invariant; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.invariant _) (fun s => snapshot s = initial))
    | (ordinary_head Leanux.unsupported; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.unsupported _) (fun s => snapshot s = initial))
    | ordinary_strict_step

theorem wgCreate_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgCreate
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgCreate_ordinary ).wp P hp

theorem wgDestruct_ordinary  : OrdinaryAction wgDestruct := by
  unfold wgDestruct
  repeat' first
    | (ordinary_head Leanux.retireDeviceUnits; apply SameView.ordinary; exact sameSnapshot_of_sameWGStore Framing.retireDeviceUnits_sameWGStore)
    | (ordinary_head modify; exact clearDevice_ordinary)
    | (ordinary_head Leanux.WG.peerRemoveAll; with_reducible exact @peerRemoveAll_ordinary)
    | (ordinary_head Leanux.WG.socketReinit; refine SameView.ordinary ?_; with_reducible exact @socketReinit_sameSnapshot _ _)
    | (ordinary_head Leanux.WG.getDev; refine SameView.ordinary ?_; with_reducible exact @getDev_sameSnapshot)
    | (ordinary_head Leanux.WG.mayHaveSlept; refine SameView.ordinary ?_; with_reducible exact @mayHaveSlept_sameSnapshot)
    | (ordinary_head Leanux.WG.ratelimiterUninit; refine SameView.ordinary ?_; with_reducible exact @ratelimiterUninit_sameSnapshot)
    | (ordinary_head Leanux.branch; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) (fun s => snapshot s = initial))
    | (ordinary_head Leanux.branchCmp; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.branchCmp _ _ _ _) (fun s => snapshot s = initial))
    | (ordinary_head Leanux.branchCmpExcluded; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.branchCmpExcluded _ _ _) (fun s => snapshot s = initial))
    | (ordinary_head Leanux.invariant; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.invariant _) (fun s => snapshot s = initial))
    | (ordinary_head Leanux.unsupported; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.unsupported _) (fun s => snapshot s = initial))
    | ordinary_strict_step

theorem wgDestruct_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ wgDestruct
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgDestruct_ordinary ).wp P hp

theorem wgDelete_ordinary  : OrdinaryAction wgDelete := by
  unfold wgDelete getWG
  simp (config := { zeta := false }) only [liftM, monadLift_self]
  transition_ordinary [] using [getDev_sameSnapshot, mayHaveSlept_sameSnapshot, wgDown_ordinary, wgDestruct_ordinary]

theorem wgDelete_spec (P : Snapshot → Prop) (hp : Stable P)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (wgDelete : WG.M Int)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgDelete_ordinary ).wp P hp

theorem wgXmit_ordinary (family addr : Nat) (pkts : List Packet) (mtu : Nat) : OrdinaryAction (wgXmit family addr pkts mtu) := by
  have routingOrdinary (α : Type) (a : Net.M α) :
      OrdinaryAction (monadLift a : WG.M α) := by
    apply SameView.ordinary
    intro initial
    exact hoare_liftRouting a (fun w => snapshot w = initial) (fun _ _ h => h)
  unfold wgXmit
  simp (config := { zeta := false }) only [liftM]
  repeat' first
    | (ordinary_head Leanux.WG.sendStagedPackets; with_reducible exact @sendStagedPackets_ordinary _)
    | (ordinary_head Leanux.WG.lookupDst; refine SameView.ordinary ?_; with_reducible exact @lookupDst_sameSnapshot _ _)
    | (ordinary_head Leanux.WG.getPeer; refine SameView.ordinary ?_; with_reducible exact @getPeer_sameSnapshot _)
    | (ordinary_head Leanux.WG.setPeer; refine SameView.ordinary ?_; with_reducible exact @setPeer_sameSnapshot _ _)
    | (ordinary_head Leanux.WG.peerPut; refine SameView.ordinary ?_; with_reducible exact @peerPut_sameSnapshot _)
    | (ordinary_head Leanux.envOk; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.envOk _) (fun s => snapshot s = initial))
    | (ordinary_head Leanux.skipCutSites; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.skipCutSites _) (fun s => snapshot s = initial))
    | (ordinary_head Leanux.WG.loopbackSend; refine SameView.ordinary ?_; with_reducible exact @loopbackSend_sameSnapshot _ _)
    | (ordinary_head Leanux.branch; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) (fun s => snapshot s = initial))
    | (ordinary_head Leanux.branchCmp; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.branchCmp _ _ _ _) (fun s => snapshot s = initial))
    | (ordinary_head Leanux.branchCmpExcluded; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.branchCmpExcluded _ _ _) (fun s => snapshot s = initial))
    | (ordinary_head Leanux.invariant; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.invariant _) (fun s => snapshot s = initial))
    | (ordinary_head Leanux.unsupported; apply SameView.ordinary; intro initial; exact hoare_liftAmbient (AmbientM.unsupported _) (fun s => snapshot s = initial))
    | ordinary_strict_step
  all_goals exact routingOrdinary _ _

theorem wgXmit_spec (P : Snapshot → Prop) (hp : Stable P) (family addr : Nat) (pkts : List Packet) (mtu : Nat) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (wgXmit family addr pkts mtu)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (wgXmit_ordinary family addr pkts mtu).wp P hp

theorem setMtu_sameSnapshot (mtu : Int) : SameSnapshot (setMtu mtu) := by
  snapshot_source [setMtu] using []

theorem setMtu_spec (P : Snapshot → Prop) (mtu : Int) :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ (setMtu mtu)
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (setMtu_sameSnapshot mtu).wp P

theorem netnsPreExit_sameSnapshot  : SameSnapshot netnsPreExit := by
  snapshot_source [netnsPreExit] using [getDev_sameSnapshot, socketReinit_sameSnapshot, clearPeerEndpointSrc_sameSnapshot]

theorem netnsPreExit_spec (P : Snapshot → Prop)  :
    ⦃fun w => ⌜P (snapshot w)⌝⦄ netnsPreExit
    ⦃⇓? _ w => ⌜P (snapshot w)⌝⦄ := (netnsPreExit_sameSnapshot ).wp P

end Leanux.Proofs.WG.Keypairs.WGDevice
