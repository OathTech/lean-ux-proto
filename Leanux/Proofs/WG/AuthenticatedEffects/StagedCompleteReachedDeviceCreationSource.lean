import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecycleMetadataCanonical

/-! The original newlink body is factored at fixed native continuations.
The epoch write and its following Ambient-only suffix have explicit points;
no point assumes its packet account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DeviceCreation
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity TransmitSecurity Queues.RxCredits

def unwind : WG.M (Except Int Nat) := unsupported "wg_newlink's unwinding after an allocation failure"

def afterQueues : WG.M (Except Int Nat) := do
  skipCut allocCuts
  let ret ← ratelimiterInit
  if ← branch .newlinkRatelimiterErr (ret < 0) then return ← unwind
  -- register_netdevice: the ifindex (the netns cursor, dev.c:10000-10018),
  -- netdev_register_kobject's uevents (alloc_uevent_skb, below the cut),
  -- then NETDEV_REGISTER, whose inetdev_init and ipv6_add_dev each draw a
  -- neighbour parms' reachable time (a cut: unobserved); between the two,
  -- devinet_sysctl_register's netconf notification (nlmsg_new, a below-cut
  -- allocation recorded when the run armed __alloc_skb), after them the
  -- IPv6 and link notifications (consumed by rtnetlinkRequest's cut)
  let ok ← envOk .registerNetdevice
  if ← branch .newlinkRegisterErr !ok then return ← unwind
  let ifindex := (← get).netIfindexNext
  modify fun k => { k with netIfindexNext := ifindex + 1 }
  pure (.ok ifindex)

def afterWorkqueues : WG.M (Except Int Nat) := do
  if ← branch .newlinkEncryptQueueErr !(← envOk .packetQueueInit) then return ← unwind
  if ← branch .newlinkDecryptQueueErr !(← envOk .packetQueueInit) then return ← unwind
  if ← branch .newlinkHandshakeQueueErr !(← envOk .packetQueueInit) then return ← unwind
  -- below the cut when the run armed kvmalloc: alloc_netdev_mqs's device
  -- (before wg_newlink) and the encrypt and decrypt queues' ptr rings
  -- (`AllocSite.netdevAlloc`, `.ptrRingInit`), before the ratelimiter's key
  afterQueues

def afterHash : WG.M (Except Int Nat) := do
  if ← branch .newlinkIndexHashtableErr !(← envOk .indexHashtableAlloc) then return ← unwind
  -- three alloc_workqueue: only packet_crypt_wq (WQ_MEM_RECLAIM) gets a
  -- rescuer, whose kthread_create the task waits for (a sleep point)
  if ← branch .newlinkRecvWqErr !(← envOk .allocWorkqueue) then return ← unwind
  if ← branch .newlinkSendWqErr !(← envOk .allocWorkqueue) then return ← unwind
  let crypt ← envOk .allocWorkqueue
  mayHaveSlept
  if ← branch .newlinkCryptWqErr !crypt then return ← unwind
  afterWorkqueues

def front : WG.M (Except Int Nat) := do
  modifyDev fun d => { d with creatingNet := true }   -- rcu_assign_pointer(wg->creating_net, src_net)
  -- wg_allowedips_init: empty tries, seq 1 (the fresh device's)
  cookieCheckerInit
  modifyDev fun d => { d with deviceUpdateGen := 1 }
  if ← branch .newlinkPeerHashtableErr !(← pubkeyHashtableAlloc) then return .error (-ENOMEM)
  afterHash

def afterIndex : WG.M Int := do
  skipCutExactly .neighReachTime 2 allocCuts
  pure 0

def finish : Except Int Nat → WG.M Int
  | .error err=>pure err
  | .ok ifindex=>do
      modifyDev fun d=>{d with ifindex}
      afterIndex

theorem source : wgNewlink=(front >>= finish) := by
  simp only [wgNewlink,front,afterHash,afterWorkqueues,afterQueues,unwind,bind_assoc]
  repeat' first
    | rfl
    | apply RxWorkers.bind_congr
    | maintenance_intro
    | split
    | dsimp (config := {failIfUnchanged := true}) only [finish,afterIndex]
    | simp (config := {failIfUnchanged := true}) only [bind_assoc,TxDisposition.bind_ite,pure_bind]

noncomputable def afterQueuesShape : PeerMetadata.Shape afterQueues := by
  unfold afterQueues
  repeat' first
    | (metadata_source_head ratelimiterInit; exact PeerMetadata.limiterInitShape)
    | unfold unwind
    | lifecycle_metadata_step

noncomputable def afterWorkqueuesShape : PeerMetadata.Shape afterWorkqueues := by
  unfold afterWorkqueues
  repeat' first
    | (metadata_source_head afterQueues; exact afterQueuesShape)
    | unfold unwind
    | lifecycle_metadata_step

noncomputable def afterHashShape : PeerMetadata.Shape afterHash := by
  unfold afterHash
  repeat' first
    | (metadata_source_head afterWorkqueues; exact afterWorkqueuesShape)
    | unfold unwind
    | lifecycle_metadata_step

noncomputable def frontShape : PeerMetadata.Shape front := by
  unfold front
  repeat' first
    | (metadata_source_head afterHash; exact afterHashShape)
    | (metadata_source_head cookieCheckerInit; exact PeerMetadata.cookieInitShape)
    | (metadata_source_head pubkeyHashtableAlloc; exact PeerMetadata.pubkeyAllocShape)
    | lifecycle_metadata_step

noncomputable def afterIndexShape : PeerMetadata.Shape afterIndex := by
  unfold afterIndex
  repeat' metadata_source_step

inductive Point : WGWorld → Ambient → WGWorld → Ambient → Prop where
  | front (point : PeerMetadata.Point frontShape w a v b) : Point w a v b
  | afterIndex (prepared : (DeviceCreation.front.run w).run a=.ok ((.ok ifindex,u),c))
      (written : ((modifyDev fun d=>{d with ifindex}).run u).run c=.ok (((),x),e))
      (point : PeerMetadata.Point afterIndexShape x e v b) : Point w a v b
  | returned (performed : (wgNewlink.run w).run a=.ok ((result,v),b)) : Point w a v b

theorem Point.remaining (point : Point w a v b) :
    ∃rest : WG.M Int,(wgNewlink.run w).run a=(rest.run v).run b := by
  cases point with
  | front point=>
      obtain ⟨rest,same⟩:=point.remaining
      exact ⟨rest >>= finish,by rw [source];simp only [StateT.run_bind,same]⟩
  | afterIndex prepared written point=>
      obtain ⟨rest,same⟩:=point.remaining
      refine ⟨rest,?_⟩
      rw [source]
      simp only [StateT.run_bind,prepared]
      change (((modifyDev _ >>= fun _=>DeviceCreation.afterIndex).run _).run _)=_
      simp only [StateT.run_bind,written]
      exact same
  | returned performed=>exact ⟨pure _,performed⟩

theorem Point.lifted_remaining {E : Type} {w : World} (point : Point w.wg w.ambient v b) (h : List E) :
    ∃rest : PrefixM E Int,runPrefix (liftPrefix (liftWG wgNewlink)) w h=
      runPrefix rest {w with wg:=v,ambient:=b} h := by
  obtain ⟨rest,same⟩:=point.remaining
  refine ⟨liftWGObserver (liftWGPrefix rest),?_⟩
  rw [←liftWGObserver_lift]
  simp only [liftWGObserver_run,runWGPrefix_lift,same]

noncomputable def remainder {E : Type} {w : World} (h : List E) (point : Point w.wg w.ambient v b) : PrefixM E Int :=
  Classical.choose (point.lifted_remaining h)

theorem remainder_run {E : Type} {w : World} (h : List E) (point : Point w.wg w.ambient v b) :
    runPrefix (liftPrefix (liftWG wgNewlink)) w h=runPrefix (remainder h point) {w with wg:=v,ambient:=b} h :=
  Classical.choose_spec (point.lifted_remaining h)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DeviceCreation
