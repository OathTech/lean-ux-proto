import Leanux.Proofs.Framing.EnvOperations
import Leanux.Proofs.WG.Lifetimes.AllocationInitial
import Leanux.Proofs.WG.Lifetimes.EnvDeferredCalls
import Leanux.Proofs.WG.Lifetimes.DeviceLifecycle

/-! Product environment controls retain the actual routing notifications,
device callbacks and failure prefixes. Focused native calls record resident
accesses; typed routing and ambient lifts retain their actual state effects. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem envScalar_identity_metadata (w v : World) (he : envScalarView v = envScalarView w) :
    (identityView v.wg, allocationMetadata v.wg) = (identityView w.wg, allocationMetadata w.wg) := by
  let observe : WGStoreView → IdentityView := fun s =>
    (⟨s.peerCounter, fun i => (s.dev.bind fun d => d.peers[i]?).map (·.internalId)⟩,
      (fun i => (s.dev.bind fun d => d.keypairs[i]?).map (·.internalId)),
      fun slot => s.dev.bind fun d => match slot with
        | .inl i => d.txSkbs[i]?.map (fun _ => (d.ifindex, i + 1))
        | .inr i => d.rxSkbs[i]?.map (fun _ => (d.ifindex, i + 1)))
  have hs := congrArg (fun s : ProductStore43 => s.2.2.2) he
  have hi := congrArg observe hs
  have hm := congrArg (fun s : WGStoreView =>
    (⟨s.keypairCounter, s.netIfindexNext,
      s.dev.map deviceAllocationMetadata⟩ : AllocationMetadata)) hs
  apply Prod.ext
  · apply Prod.ext
    · simpa [observe, identityView, Peers.snapshot, envScalarView, envScalarStore,
        productStoreView, envScalarDevice, wgStoreView, Option.bind_map, Function.comp_def] using congrArg Prod.fst hi
    · apply Prod.ext
      · change keypairResidents v.wg = keypairResidents w.wg
        unfold keypairResidents
        simpa [observe, envScalarView, envScalarStore, productStoreView, envScalarDevice,
          wgStoreView, Option.bind_map, Function.comp_def] using
          congrArg (fun s : IdentityView => s.2.1) hi
      · funext slot
        have ht := congrArg (fun s : IdentityView => s.2.2 slot) hi
        cases slot <;>
          simpa [observe, identityView, packetResidents, envScalarView, envScalarStore, productStoreView,
            envScalarDevice, wgStoreView, Option.bind_map, Function.comp_def] using ht
  · unfold allocationMetadata deviceAllocationMetadata
    simpa [deviceAllocationMetadata, envScalarView, envScalarStore, productStoreView,
      envScalarDevice, wgStoreView, Option.map_map, Function.comp_def] using hm

abbrev setMtuAudit (mtu : Nat) : AuditM Int := liftPrefix (Env.setMtu mtu)
abbrev routeIntoWg0Audit : AuditM Unit := liftPrefix Env.routeIntoWg0
abbrev wgDeladdrAudit (family : Nat) : AuditM Int := liftPrefix (Env.wgDeladdr family)
abbrev wgDelrouteAudit (family : Nat) : AuditM Int := liftPrefix (Env.wgDelroute family false 0 0 0 0 0)

def observeAudit : AuditM (Int × Lean.Json) := do
  idleTimersAudit
  liftPrefix Environment.observeTail

def envWgUpAudit : AuditM Int := do
  let some d := (← liftPrefix getWG).dev | return -ENODEV
  if d.running then return 0
  let ret ← auditFocus (liftWGObserver wgUpPrefix)
  liftPrefix (skipCut allocCuts)
  if ret == 0 then
    liftPrefix Net.Fib.rtCacheFlush
    liftPrefix (Net.Fib.netdevUp WG0_IFINDEX)
  if ret == 0 then liftPrefix (modifyEnv fun w => { w with routesPending := true })
  return ret

def envWgDownAudit : AuditM Int := do
  let some d := (← liftPrefix getWG).dev | return -ENODEV
  if !d.running then return 0
  auditFocus requireIdleDevicePrefix
  auditFocus (liftWGObserver wgDownPrefix)
  liftPrefix (skipCut allocCuts)
  liftPrefix Net.Fib.rtCacheFlush
  liftPrefix (Net.Fib.netdevDown WG0_IFINDEX)
  liftPrefix (modifyRouting fun w => { w with defaultRoute6 := false, addrs6 := [], ipv6Gen := w.ipv6Gen + 1 })
  return 0

def envWgDeleteAudit : AuditM Int := do
  if (← liftPrefix getWG).dev.isSome then auditFocus requireIdleDevicePrefix
  let pending (sock : WG.NlSock) : Bool :=
    sock.cbRunning || sock.queue.any fun chunk => chunk.messages.any fun m => match m with | .done .. => true | _ => false
  let k ← liftPrefix getWG
  if pending k.nlSock7 || pending k.nlSock8 then
    liftPrefix (unsupported "a delete with a stepped dump pending (the dump's cursor holds the device reference; the guest refuses wg_delete_with_dump_pending)")
  let onDown : AuditM Unit := do
    liftPrefix Net.Fib.rtCacheFlush
    liftPrefix (Net.Fib.netdevDown WG0_IFINDEX)
    liftPrefix (modifyRouting fun w => { w with defaultRoute6 := false, addrs6 := [], ipv6Gen := w.ipv6Gen + 1 })
  let onUnregister : AuditM Unit := do
    liftPrefix Env.inetdevDestroy
    liftPrefix (Net.Fib.netdevUnregister WG0_IFINDEX)
    liftPrefix (modifyRouting fun w => { w with addrs6 := [], defaultRoute6 := false, ipv6Gen := w.ipv6Gen + 1 })
  if (← liftPrefix getWG).dev.isNone then return -ENODEV
  if (← liftPrefix (liftWG getDev)).running then
    auditFocus (liftWGObserver wgDownPrefix)
    onDown
  liftPrefix (skipCut allocCuts)
  onUnregister
  liftPrefix (liftWG mayHaveSlept)
  auditFocus (liftWGObserver wgDestructPrefix)
  return 0

def envNetnsCleanupAudit : AuditM Unit := do
  if !(← liftPrefix getRouting).foreignCreator then liftPrefix (unsupported "wg_netns_close outside the foreign-creator fixture")
  if !(← liftPrefix (Env.pendingDevice .netnsCleanup false)) then
    liftPrefix (invariant "cleanup_net: its section run with no unit queued (the pin's last release did not run)")
  if let some u ← liftPrefix (peekUnit .netnsCleanup) then _ ← liftPrefix (resolveUnit .netnsCleanup u [0])
  runWorkerPrefix .netnsCleanup do
    auditFocus (liftWGObserver netnsPreExitPrefix)
    liftPrefix (Net.Fib.inCreatorNs do
      Net.Fib.rtCacheFlush
      Net.Fib.netdevDown LO_IFINDEX
      Net.Fib.inetaddrDown LO_IFINDEX LOOPBACK4 8 true true
      Net.Fib.netdevUnregister LO_IFINDEX)
    liftPrefix (skipCut ([.dstCacheResetTs] ++ allocCuts))

theorem setMtuAudit_erases (mtu : Nat) : ErasesPrefix (setMtuAudit mtu) (Env.setMtu mtu) := erasesPrefix_lift _
theorem routeIntoWg0Audit_erases : ErasesPrefix routeIntoWg0Audit Env.routeIntoWg0 := erasesPrefix_lift _
theorem wgDeladdrAudit_erases (family : Nat) : ErasesPrefix (wgDeladdrAudit family) (Env.wgDeladdr family) := erasesPrefix_lift _
theorem wgDelrouteAudit_erases (family : Nat) : ErasesPrefix (wgDelrouteAudit family) (Env.wgDelroute family false 0 0 0 0 0) := erasesPrefix_lift _
theorem observeAudit_erases : ErasesPrefix observeAudit Env.observe := by
  rw [Environment.observe_eq]
  exact erasesPrefix_bind idleTimersAudit_erases (fun _ => erasesPrefix_lift _)

theorem setMtuAudit_preserves (mtu : Nat) : PrefixPreserves AuditInv AuditSafe (setMtuAudit mtu) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  have hf := envScalar_identity_metadata w v ((ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar mtu) w x v hr)
  exact ⟨hi.1.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf), hi.2⟩

theorem routeIntoWg0Audit_preserves : PrefixPreserves AuditInv AuditSafe routeIntoWg0Audit :=
  auditLift_store _ (routeIntoWg0_sameKernel.of_factor
    (fun s : ProductStore43 => s.2.2.2) (fun w => wgStoreView w.wg) (fun _ => rfl))
theorem wgDeladdrAudit_preserves (family : Nat) : PrefixPreserves AuditInv AuditSafe (wgDeladdrAudit family) :=
  auditLift_store _ ((wgDeladdr_sameKernel family).of_factor
    (fun s : ProductStore43 => s.2.2.2) (fun w => wgStoreView w.wg) (fun _ => rfl))
theorem wgDelrouteAudit_preserves (family : Nat) : PrefixPreserves AuditInv AuditSafe (wgDelrouteAudit family) :=
  auditLift_store _ ((wgDelroute_sameKernel family).of_factor
    (fun s : ProductStore43 => s.2.2.2) (fun w => wgStoreView w.wg) (fun _ => rfl))
theorem observeAudit_preserves : PrefixPreserves AuditInv AuditSafe observeAudit :=
  PrefixPreserves.bind idleTimersAudit_preserves (fun _ => auditLift_store _
    (observeTail_sameKernel.of_factor (fun s : ProductStore43 => s.2.2.2)
      (fun w => wgStoreView w.wg) (fun _ => rfl)))

macro "control_audit_erases" : tactic => `(tactic|
  first
    | maintenance_intro
    | contradiction
    | timer_audit_stopped
    | (timer_audit_focus_head wgUpPrefix; exact auditFocus_erases (liftWGObserver_erases wgUpPrefix_erases))
    | (timer_audit_focus_head wgDownPrefix; exact auditFocus_erases (liftWGObserver_erases wgDownPrefix_erases))
    | (timer_audit_focus_head wgDestructPrefix; exact auditFocus_erases (liftWGObserver_erases wgDestructPrefix_erases))
    | (timer_audit_focus_head netnsPreExitPrefix; exact auditFocus_erases (liftWGObserver_erases netnsPreExitPrefix_erases))
    | (maintenance_head auditFocus; exact auditFocus_erases requireIdleDevicePrefix_erases)
    | (maintenance_head runWorkerPrefix; apply runWorkerPrefix_erases)
    | (maintenance_head liftPrefix; exact erasesPrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesPrefix_pure _)
    | (maintenance_head Bind.bind; apply erasesPrefix_bind)
    | (maintenance_head ite; apply erasesPrefix_ite)
    | timer_audit_erases_join
    | timer_audit_erases_join_use
    | timer_audit_reduce
    | timer_audit_reduce_match
    | timer_audit_cases
    | (with_reducible split))

elab "control_audit_routing" : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := target.getAppArgs
  unless target.isAppOf ``PrefixEnsures && args.size ≥ 2 do Lean.throwError "not a prefix contract"
  let action := args[args.size - 2]!.consumeMData
  unless action.isAppOf ``liftPrefix do Lean.throwError "not a product lift"
  let rec name (fuel : Nat) (e : Lean.Expr) : Lean.Name :=
    match fuel with
    | 0 => .anonymous
    | n+1 =>
      let e := e.consumeMData
      match e.getAppFn with
      | .const actual _ =>
        if actual == ``liftM || actual == ``MonadLift.monadLift || actual == ``MonadLiftT.monadLift then
          if e.getAppArgs.isEmpty then .anonymous else name n e.getAppArgs.back!
        else actual
      | _ => .anonymous
  let actual := name 4 action.getAppArgs.back!
  unless actual == ``getRouting || actual == ``modifyRouting ||
      actual.toString.startsWith "Leanux.Net." do Lean.throwError "not a routing lift"

/-- The pending-unit test the namespace close and cleanup make (2026-10-20):
an ambient read, then a pure answer; the WireGuard store is untouched. -/
theorem pendingDevice_sameWGStore (w : Worker) (queued : Bool) :
    SameView (fun w : World => wgStoreView w.wg) (Env.pendingDevice w queued) := by
  unfold Env.pendingDevice
  exact SameView.bind (fun _ => productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ hi => hi))
    (fun _ => SameView.pure _ _)

macro "control_audit_store" : tactic => `(tactic|
  first
    | (audit_contract_head Env.pendingDevice; exact auditLift_store _ (pendingDevice_sameWGStore _ _))
    | (audit_contract_head getWG; exact auditLift_store _ (by
        intro initial
        exact productGetWG_spec (fun s => s.2.2.2 = initial)))
    | (audit_contract_head modifyEnv; exact auditLift_store _ (by
        apply (ProjectedAction.iff_run _ _ _).mpr
        intro w x v hr
        cases hr
        rfl))
    | (audit_contract_head liftWG; first
        | exact auditLift_store _ (sameView_liftWG (fun w => wgStoreView w.wg)
            wgStoreView getDev getDev_sameWGStore (fun _ _ _ hi => hi))
        | exact auditLift_store _ (sameView_liftWG (fun w => wgStoreView w.wg)
            wgStoreView mayHaveSlept mayHaveSlept_sameWGStore (fun _ _ _ hi => hi)))
    | (control_audit_routing; exact auditLift_store _ (by
        intro initial
        exact productRouting_spec _ (fun s => s.2.2.2 = initial)))
    | (audit_contract_head liftPrefix; exact auditLift_store _ (by
        intro initial
        exact productAmbient_spec _ _ (fun _ _ hi => hi))))

macro "control_audit_preserves" : tactic => `(tactic|
  first
    | maintenance_intro
    | contradiction
    | timer_audit_stopped
    | (timer_audit_focus_head wgUpPrefix; exact auditFocus_preserves
        (wgUpPrefix_preserves allocationAmbient allocationDeviceControl).liftWGObserver)
    | (timer_audit_focus_head wgDownPrefix; exact auditFocus_preserves
        (wgDownPrefix_preserves allocationAmbient allocationDeviceControl).liftWGObserver)
    | (timer_audit_focus_head wgDestructPrefix; exact auditFocus_preserves
        (wgDestructPrefix_preserves allocationAmbient allocationDeviceLifecycle).liftWGObserver)
    | (timer_audit_focus_head netnsPreExitPrefix; exact auditFocus_preserves
        (netnsPreExitPrefix_preserves allocationAmbient allocationDeviceControl).liftWGObserver)
    | (audit_contract_head requireIdleDevicePrefix; exact auditFocus_preserves requireIdleDevicePrefix_allocation)
    | (audit_contract_head runWorkerPrefix; apply runWorkerPrefix_preserves
        (fun _ _ hi => hi.safe) (fun _ _ _ he hi =>
          hi.store (congrArg (fun s : ProductStore43 => s.2.2.2) he)))
    | control_audit_store
    | (audit_contract_head Pure.pure; exact PrefixEnsures.pure (fun _ _ hi => hi.safe) (fun _ _ hi => hi))
    | (audit_contract_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => AuditInv h w))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | (with_reducible split))

theorem envWgUpAudit_erases : ErasesPrefix envWgUpAudit Env.wgUp := by
  unfold envWgUpAudit Env.wgUp
  repeat' control_audit_erases

theorem envWgUpAudit_preserves : PrefixPreserves AuditInv AuditSafe envWgUpAudit := by
  apply PrefixEnsures.preserves
  unfold envWgUpAudit
  repeat' control_audit_preserves

theorem envWgDownAudit_erases : ErasesPrefix envWgDownAudit Env.wgDown := by
  unfold envWgDownAudit Env.wgDown
  repeat' control_audit_erases

theorem envWgDownAudit_preserves : PrefixPreserves AuditInv AuditSafe envWgDownAudit := by
  apply PrefixEnsures.preserves
  unfold envWgDownAudit
  repeat' control_audit_preserves

theorem envWgDeleteAudit_erases : ErasesPrefix envWgDeleteAudit Env.wgDelete := by
  unfold envWgDeleteAudit Env.wgDelete WG.wgDelete
  repeat' control_audit_erases

theorem envWgDeleteAudit_preserves : PrefixPreserves AuditInv AuditSafe envWgDeleteAudit := by
  have hi : PrefixPreserves AuditInv AuditSafe (liftPrefix Env.inetdevDestroy) := by
    apply auditLift_store
    unfold Env.inetdevDestroy
    apply SameView.bind
    · intro initial
      exact productRouting_spec (getRouting : Net.M Net.Routing) (fun s => s.2.2.2 = initial)
    intro routing
    apply SameView.bind
    · intro initial
      exact productRouting_spec (modifyRouting fun s => {s with addrs4 := [], addrPlens4 := []}) (fun s => s.2.2.2 = initial)
    intro _
    apply SameView.bind
    · apply Framing.DumpComposition.forIn_sameView
      intro a rest
      apply SameView.bind
      · intro initial
        exact productRouting_spec (Net.Fib.inetaddrDown WG0_IFINDEX a ((routing.addrPlens4.lookup a).getD 32) (rest.drop 1).isEmpty true)
          (fun s => s.2.2.2 = initial)
      intro _
      exact SameView.pure _ _
    intro _
    exact SameView.pure _ _
  apply PrefixEnsures.preserves
  unfold envWgDeleteAudit
  repeat' first
    | (audit_contract_head Env.inetdevDestroy; exact hi)
    | control_audit_preserves

theorem envNetnsCleanupAudit_erases : ErasesPrefix envNetnsCleanupAudit Env.netnsCleanup := by
  unfold envNetnsCleanupAudit Env.netnsCleanup
  repeat' control_audit_erases

theorem envNetnsCleanupAudit_preserves : PrefixPreserves AuditInv AuditSafe envNetnsCleanupAudit := by
  apply PrefixEnsures.preserves
  unfold envNetnsCleanupAudit
  repeat' control_audit_preserves

end Leanux.Proofs.WG.Lifetimes
