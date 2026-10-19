import Leanux.Proofs.WG.RetirementSecurity.HolderDumpDispatch

/-! Native poll-free dispatch leaves preserve the key account through their
actual descriptor and netlink wrappers. Each caller uses only the support its
source needs; quiet operations are framed over the WG store projection. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderDispatch
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

def StoreStable (P : World→Prop) := ∀w v,wgStoreView v.wg=wgStoreView w.wg→P w→P v

theorem socket (P : World→Prop) (store : StoreStable P) (fd : Nat) (body : Leanux.M Int)
    (keeps : Preserves P body) : Preserves P (socketCallOn fd body) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryPollFree.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryPollFree.socket_spec)
    P store fd body keeps

theorem rtnetlink (P : World→Prop) (store : StoreStable P) (body : Leanux.M Int)
    (keeps : Preserves P body) : Preserves P (rtnetlinkRequest body) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryPollFree.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryPollFree.rtnetlink_spec)
    P store body keeps

theorem ambient (P : World→Prop) (store : StoreStable P) (action : AmbientM α) : Preserves P (liftAmbient action) :=
  productAmbient_spec action P (fun w _ entry=>store w _ rfl entry)

theorem netlink (P : World→Prop) (store : StoreStable P) (body : Leanux.M Int)
    (keeps : Preserves P body) : Preserves P (netlinkRequest body) := by
  unfold netlinkRequest socketCall
  apply preserves_bind (socket P store _ _ (preserves_bind (ambient P store (AmbientM.skipCut allocCuts))
    (fun _=>preserves_bind keeps (fun ret=>preserves_bind (ambient P store (AmbientM.skipCut allocCuts))
    (fun _=>preserves_pure ret)))))
  intro ret
  exact preserves_bind (socket P store _ _ (preserves_pure 0)) (fun _=>preserves_pure ret)

theorem key_store : StoreStable (fun w : World=>HolderAccount temporary w.wg) :=
  fun _ _ same entry=>HolderPoll.keys_store entry same

theorem boundary_store : StoreStable (fun w : World=>HolderBoundary.Entry temporary carriers loans w.wg) :=
  fun _ _ same entry=>HolderLifecycle.boundary_store entry same

theorem configuration (attrs : DeviceAttrs) :
    Preserves (fun w : World=>HolderBoundary.Entry temporary carriers loans w.wg) (dispatch (.wgSet attrs)) :=
  netlink _ boundary_store _ (PublicationPoll.native_product _ _ (HolderBoundary.device attrs))

theorem up : Preserves (fun w : World=>HolderBoundary.Entry temporary carriers loans w.wg) (dispatch .wgUp) :=
  socket _ boundary_store _ _ HolderLifecycle.env_up

theorem down : Preserves (fun w : World=>HolderBoundary.Entry temporary carriers loans w.wg) (dispatch .wgDown) :=
  socket _ boundary_store _ _ HolderLifecycle.env_down

theorem create : Preserves (fun w : World=>HolderAccount [] w.wg) (dispatch .wgCreate) :=
  rtnetlink _ key_store _ (PublicationPoll.native_product _ _ HolderLifecycle.create)

theorem mtu_keys (n : Nat) : Preserves (fun w : World=>HolderAccount temporary w.wg) (Env.setMtu n) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  apply entry.points
  have same := (ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar n) w result v run
  rw [←HolderOuter.scalar_points v,←HolderOuter.scalar_points w,same]

theorem mtu (n : Nat) : Preserves (fun w : World=>HolderAccount temporary w.wg) (dispatch (.wgSetMtu n)) :=
  socket _ key_store _ _ (mtu_keys n)

def Deletion (carriers : Ledger) (w : World) :=
  DeviceAuxEntry.Entry carriers [] w.wg ∧ HolderAccount [] w.wg

theorem deletion_store : StoreStable (Deletion carriers) :=
  fun _ _ same entry=>⟨HolderEntryFrames.store entry.1 same,HolderPoll.keys_store entry.2 same⟩

theorem deletion : Preserves (Deletion carriers) Env.wgDelete := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  have peer := (hoare_iff_run _ _ _).mp
    (pinned_const _private.Leanux.Proofs.WG.Queues.HolderEntryPollFree.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderEntryPollFree.deletion_entry)
    w result v entry.1 run
  obtain ⟨_,absent,_⟩ := HolderDeviceDelete.delete_normal w v entry.1.1.1 entry.1.2.1 run
  exact ⟨peer,HolderLifecycle.absent v.wg absent⟩

theorem delete : Preserves (Deletion carriers) (dispatch .wgDelete) :=
  rtnetlink _ deletion_store _ deletion

theorem ready_store : StoreStable (fun w : World=>HolderKeepalive.Ready temporary w.wg) := by
  intro w v same entry
  exact ⟨HolderPoll.keys_store entry.1 same,entry.2.1.store same,
    CurrentSlots.fields_transport entry.2.2 (congrArg (fun s : WGStoreView=>CurrentSlots.fields {dev:=s.dev}) same)⟩

theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (HolderKeepalive.Ready temporary) (wgXmit family addr packets mtu) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b entry run
  exact ⟨entry.1.transmit entry.2.1.bounded (CurrentSlots.current entry.2.2).compatible
    family addr packets mtu a b run,entry.2.1.transmit family addr packets mtu a b run,
    (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.wgXmit_preserves family addr packets mtu) w a result v b entry.2.2 run⟩

theorem ready_product {action : Leanux.M α} (same : SameProductStore action) :
    Preserves (fun w : World=>HolderKeepalive.Ready temporary w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  exact ready_store w v (congrArg (fun s : ProductStore43=>s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp same w result v run)) entry

theorem xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Preserves (fun w : World=>HolderKeepalive.Ready temporary w.wg) (dispatch (.wgXmit family addr payload opts)) := by
  unfold dispatch socketCallOn
  simp (config:={zeta:=false}) only [unsupported,Env.fixtureSend,skipCut]
  repeat' first
    | (allocation_release_lift_from WG.M; exact PublicationPoll.native_product _ _ (transmit _ _ _ _))
    | (rx_retention_head Env.xmitMulticastLoop; exact ready_product
        ((pinned_const _private.Leanux.Proofs.WG.Queues.BatchAccount.«0».Leanux.Proofs.WG.Queues.RxCredits.BatchAccount.multicast_store) _ _))
    | (rx_retention_head Env.xmitPackets; exact ready_product (xmitPackets_sameKernel _ _ _ _))
    | (rx_retention_head getWG; exact ready_product (fun initial=>productGetWG_spec (·=initial)))
    | (allocation_release_lift_from Net.M; exact ready_product (fun initial=>productRouting_spec _ (·=initial)))
    | (allocation_release_lift_from AmbientM; exact ambient _ ready_store _)
    | (allocation_release_lift_from FS.M; exact productFS_spec _ _ (fun _ _ _ _ entry=>entry))
    | rx_retention_step

end Leanux.Proofs.WG.RetirementSecurity.HolderDispatch
