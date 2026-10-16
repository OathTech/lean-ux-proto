import Leanux.Proofs.Framing.EnvOperations
import Leanux.Proofs.WG.Lifetimes.AllocationInitial
import Leanux.Proofs.WG.Lifetimes.EnvDeferredCalls
import Leanux.Proofs.WG.Lifetimes.DeviceLifecycle

/-! Remaining environment controls and exact observation. Bookkeeping lifts have
separately audited source coverage; actual device operations remain focused access
observers. All source guards, ordinary returns and Stop prefixes are retained. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem auditLift_wgKernel (a : M α) (ha : SameWGKernel a) :
    PrefixPreserves AuditInv AuditSafe (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift a (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  exact ⟨hi.1.wgKernel (ha w x v hr), hi.2⟩

theorem envScalar_identity_metadata (w v : World) (he : envScalarView v = envScalarView w) :
    (identityView v, allocationMetadata v) = (identityView w, allocationMetadata w) := by
  have hi := congrArg (fun k => identityView {w with k}) he
  have hm := congrArg (fun k => allocationMetadata {w with k}) he
  apply Prod.ext
  · unfold identityView Peers.snapshot keypairResidents packetResidents at hi ⊢
    simpa [envScalarView, envScalarKernel, envScalarDevice, Option.bind_map, Function.comp_def] using hi
  · unfold allocationMetadata deviceAllocationMetadata at hm ⊢
    simpa [envScalarView, envScalarKernel, envScalarDevice, Option.map_map, Function.comp_def] using hm

abbrev setMtuAudit (mtu : Nat) : AuditM Int := liftPrefix (Env.setMtu mtu)
abbrev routeIntoWg0Audit : AuditM Unit := liftPrefix Env.routeIntoWg0
abbrev wgDeladdrAudit (family : Nat) : AuditM Int := liftPrefix (Env.wgDeladdr family)
abbrev wgDelrouteAudit (family : Nat) : AuditM Int := liftPrefix (Env.wgDelroute family)

def observeAudit : AuditM (Int × Lean.Json) := do
  idleTimersAudit
  liftPrefix Environment.observeTail

def envWgUpAudit : AuditM Int := do
  let some d := (← liftPrefix getK).wg | return -ENODEV
  if d.running then return 0
  let ret ← auditFocus wgUpPrefix
  -- `dev_change_flags`' rtnetlink notifications and the fixture's routes
  -- allocate netlink skbs below the cut (allocation cut sites, A)
  liftPrefix (skipCut allocCuts)
  -- W9: the guest's `route_into_wg0` adds wg0's addresses and default routes
  -- after this operation's wait (design 14.3b): `routeIntoWg0` applies them
  -- once the send workers and the idle timers have run
  if ret == 0 then liftPrefix (modify fun w => { w with routesPending := true  })
  return ret


def envWgDownAudit : AuditM Int := do
  let some d := (← liftPrefix getK).wg | return -ENODEV
  if !d.running then return 0
  auditFocus requireIdleDevicePrefix
  auditFocus wgDownPrefix
  -- `__dev_close_many`'s rtnetlink notifications and the routes' removal
  -- allocate netlink skbs below the cut (allocation cut sites, A)
  liftPrefix (skipCut allocCuts)
  -- W9: NETDEV_DOWN flushes the IPv4 routes via wg0 (the address stays) and
  -- removes the IPv6 address and routes (`keep_addr_on_down` 0)
  liftPrefix (modify fun w => { w with defaultRoute4 := false, defaultRoute6 := false, addrs6 := [], ipv4Gen := w.ipv4Gen + 1, ipv6Gen := w.ipv6Gen + 1  })
  return 0


def envWgDeleteAudit : AuditM Int := do
  if (← liftPrefix getK).wg.isSome then auditFocus requireIdleDevicePrefix
  -- Pre-release review finding 6 (docs/2026-10-14-pre-release-review.md,
  -- section 6; W2 design 5): the guest refuses `wg_delete` while a stepped
  -- dump is pending (`guest.c` `wg_delete_with_dump_pending`: the dump's
  -- cursor holds the device reference, W2 C1), and the mirror's cursor does
  -- not carry that reference, so the composition is outside the domain here
  -- too, fail-closed, rather than a delete the guest would never perform.
  -- pending as the guest counts it: started, and its NLMSG_DONE not yet
  -- received (`dump_pending`, guest.c), which outlasts `cb_running` by the
  -- queued chunks
  let pending (sock : WG.NlSock) : Bool :=
    sock.cbRunning || sock.queue.any fun chunk => chunk.messages.any fun m => match m with | .done .. => true | _ => false
  let k ← liftPrefix getK
  if pending k.nlSock7 || pending k.nlSock8 then
    liftPrefix (unsupported "a delete with a stepped dump pending (the dump's cursor holds the device reference; the guest refuses wg_delete_with_dump_pending)")
  let ret ← auditFocus wgDeletePrefix
  -- W9: NETDEV_UNREGISTER removes every address and route via wg0
  liftPrefix (modify fun w => { w with addrs4 := [], addrs6 := [], defaultRoute4 := false, defaultRoute6 := false, ipv4Gen := w.ipv4Gen + 1, ipv6Gen := w.ipv6Gen + 1  })
  return ret


def envNetnsCleanupAudit : AuditM Unit := do
  if !(← liftPrefix get).foreignCreator then liftPrefix (unsupported "wg_netns_close outside the foreign-creator fixture")
  liftPrefix (modify fun w => { w with netnsCHolders := []  })
  if let some u ← liftPrefix (peekUnit .netnsCleanup) then _ ← liftPrefix (resolveUnit .netnsCleanup u [0])
  runWorkerPrefix .netnsCleanup do
    auditFocus netnsPreExitPrefix
    -- the rest of C's teardown: `sit0`'s unregister resets its tunnel's dst
    -- cache (net/ipv6/sit.c `ipip6_tunnel_uninit`: one kind-306 record, the
    -- only other consumer the section showed), and the notifications' and
    -- exits' allocations are below the cut (A)
    liftPrefix (skipCut ([.dstCacheResetTs] ++ allocCuts))


theorem setMtuAudit_erases (mtu : Nat) : ErasesPrefix (setMtuAudit mtu) (Env.setMtu mtu) := erasesPrefix_lift _
theorem routeIntoWg0Audit_erases : ErasesPrefix routeIntoWg0Audit Env.routeIntoWg0 := erasesPrefix_lift _
theorem wgDeladdrAudit_erases (family : Nat) : ErasesPrefix (wgDeladdrAudit family) (Env.wgDeladdr family) := erasesPrefix_lift _
theorem wgDelrouteAudit_erases (family : Nat) : ErasesPrefix (wgDelrouteAudit family) (Env.wgDelroute family) := erasesPrefix_lift _
theorem observeAudit_erases : ErasesPrefix observeAudit Env.observe := by
  rw [Environment.observe_eq]
  exact erasesPrefix_bind idleTimersAudit_erases (fun _ => erasesPrefix_lift _)

theorem setMtuAudit_preserves (mtu : Nat) : PrefixPreserves AuditInv AuditSafe (setMtuAudit mtu) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  have hf := envScalar_identity_metadata w v (setMtu_sameEnvScalar mtu w x v hr)
  exact ⟨hi.1.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf), hi.2⟩
theorem routeIntoWg0Audit_preserves : PrefixPreserves AuditInv AuditSafe routeIntoWg0Audit := auditLift_kernel _ routeIntoWg0_sameKernel
theorem wgDeladdrAudit_preserves (family : Nat) : PrefixPreserves AuditInv AuditSafe (wgDeladdrAudit family) := auditLift_kernel _ (wgDeladdr_sameKernel family)
theorem wgDelrouteAudit_preserves (family : Nat) : PrefixPreserves AuditInv AuditSafe (wgDelrouteAudit family) := auditLift_kernel _ (wgDelroute_sameKernel family)
theorem observeAudit_preserves : PrefixPreserves AuditInv AuditSafe observeAudit :=
  PrefixPreserves.bind idleTimersAudit_preserves (fun _ => auditLift_kernel _ observeTail_sameKernel)

theorem envWgUpAudit_erases : ErasesPrefix envWgUpAudit Env.wgUp := by
  unfold envWgUpAudit Env.wgUp
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact auditFocus_erases wgUpPrefix_erases
    | with_reducible exact auditFocus_erases wgDownPrefix_erases
    | with_reducible exact auditFocus_erases wgDeletePrefix_erases
    | with_reducible exact auditFocus_erases netnsPreExitPrefix_erases
    | with_reducible exact auditFocus_erases requireIdleDevicePrefix_erases
    | with_reducible apply runWorkerPrefix_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem envWgUpAudit_preserves : PrefixPreserves AuditInv AuditSafe envWgUpAudit := by
  unfold envWgUpAudit
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact auditFocus_preserves (wgUpPrefix_preserves allocationAmbient allocationDeviceControl)
    | with_reducible exact auditFocus_preserves (wgDownPrefix_preserves allocationAmbient allocationDeviceControl)
    | with_reducible exact auditFocus_preserves (netnsPreExitPrefix_preserves allocationAmbient allocationDeviceControl)
    | with_reducible exact auditFocus_preserves (wgDeletePrefix_preserves allocationAmbient allocationDeviceLifecycle)
    | with_reducible exact auditFocus_preserves requireIdleDevicePrefix_allocation
    | with_reducible apply runWorkerPrefix_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he)
    | with_reducible exact auditLift_kernel _ (skipCut_sameKernel _)
    | with_reducible exact auditLift_kernel _ (peekUnit_sameKernel _)
    | with_reducible exact auditLift_kernel _ (resolveUnit_sameKernel _ _ _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem envWgDownAudit_erases : ErasesPrefix envWgDownAudit Env.wgDown := by
  unfold envWgDownAudit Env.wgDown
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact auditFocus_erases wgUpPrefix_erases
    | with_reducible exact auditFocus_erases wgDownPrefix_erases
    | with_reducible exact auditFocus_erases wgDeletePrefix_erases
    | with_reducible exact auditFocus_erases netnsPreExitPrefix_erases
    | with_reducible exact auditFocus_erases requireIdleDevicePrefix_erases
    | with_reducible apply runWorkerPrefix_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem envWgDownAudit_preserves : PrefixPreserves AuditInv AuditSafe envWgDownAudit := by
  unfold envWgDownAudit
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact auditFocus_preserves (wgUpPrefix_preserves allocationAmbient allocationDeviceControl)
    | with_reducible exact auditFocus_preserves (wgDownPrefix_preserves allocationAmbient allocationDeviceControl)
    | with_reducible exact auditFocus_preserves (netnsPreExitPrefix_preserves allocationAmbient allocationDeviceControl)
    | with_reducible exact auditFocus_preserves (wgDeletePrefix_preserves allocationAmbient allocationDeviceLifecycle)
    | with_reducible exact auditFocus_preserves requireIdleDevicePrefix_allocation
    | with_reducible apply runWorkerPrefix_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he)
    | with_reducible exact auditLift_kernel _ (skipCut_sameKernel _)
    | with_reducible exact auditLift_kernel _ (peekUnit_sameKernel _)
    | with_reducible exact auditLift_kernel _ (resolveUnit_sameKernel _ _ _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem envWgDeleteAudit_erases : ErasesPrefix envWgDeleteAudit Env.wgDelete := by
  unfold envWgDeleteAudit Env.wgDelete
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact auditFocus_erases wgUpPrefix_erases
    | with_reducible exact auditFocus_erases wgDownPrefix_erases
    | with_reducible exact auditFocus_erases wgDeletePrefix_erases
    | with_reducible exact auditFocus_erases netnsPreExitPrefix_erases
    | with_reducible exact auditFocus_erases requireIdleDevicePrefix_erases
    | with_reducible apply runWorkerPrefix_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)
  all_goals contradiction

theorem envWgDeleteAudit_preserves : PrefixPreserves AuditInv AuditSafe envWgDeleteAudit := by
  unfold envWgDeleteAudit
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact auditFocus_preserves (wgUpPrefix_preserves allocationAmbient allocationDeviceControl)
    | with_reducible exact auditFocus_preserves (wgDownPrefix_preserves allocationAmbient allocationDeviceControl)
    | with_reducible exact auditFocus_preserves (netnsPreExitPrefix_preserves allocationAmbient allocationDeviceControl)
    | with_reducible exact auditFocus_preserves (wgDeletePrefix_preserves allocationAmbient allocationDeviceLifecycle)
    | with_reducible exact auditFocus_preserves requireIdleDevicePrefix_allocation
    | with_reducible apply runWorkerPrefix_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he)
    | with_reducible exact auditLift_kernel _ (skipCut_sameKernel _)
    | with_reducible exact auditLift_kernel _ (peekUnit_sameKernel _)
    | with_reducible exact auditLift_kernel _ (resolveUnit_sameKernel _ _ _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem envNetnsCleanupAudit_erases : ErasesPrefix envNetnsCleanupAudit Env.netnsCleanup := by
  unfold envNetnsCleanupAudit Env.netnsCleanup
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact auditFocus_erases wgUpPrefix_erases
    | with_reducible exact auditFocus_erases wgDownPrefix_erases
    | with_reducible exact auditFocus_erases wgDeletePrefix_erases
    | with_reducible exact auditFocus_erases netnsPreExitPrefix_erases
    | with_reducible exact auditFocus_erases requireIdleDevicePrefix_erases
    | with_reducible apply runWorkerPrefix_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem envNetnsCleanupAudit_preserves : PrefixPreserves AuditInv AuditSafe envNetnsCleanupAudit := by
  unfold envNetnsCleanupAudit
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact auditFocus_preserves (wgUpPrefix_preserves allocationAmbient allocationDeviceControl)
    | with_reducible exact auditFocus_preserves (wgDownPrefix_preserves allocationAmbient allocationDeviceControl)
    | with_reducible exact auditFocus_preserves (netnsPreExitPrefix_preserves allocationAmbient allocationDeviceControl)
    | with_reducible exact auditFocus_preserves (wgDeletePrefix_preserves allocationAmbient allocationDeviceLifecycle)
    | with_reducible exact auditFocus_preserves requireIdleDevicePrefix_allocation
    | with_reducible apply runWorkerPrefix_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he)
    | with_reducible exact auditLift_kernel _ (skipCut_sameKernel _)
    | with_reducible exact auditLift_kernel _ (peekUnit_sameKernel _)
    | with_reducible exact auditLift_kernel _ (resolveUnit_sameKernel _ _ _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Lifetimes
