import Leanux.Proofs.WG.Queues.JointDevice
import Leanux.Proofs.WG.Configuration.LifecycleCompletion
import Leanux.Proofs.WG.Lifetimes.DeviceLifecycle

/-! Device destruction keeps completed peer removals before the actual final
store retirement. The queue guards and their failed prefixes remain literal. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
universe u

def destructWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α) (remove finish : m Unit) : m Unit := do
  lift (modifyDev fun d => {d with creatingNet := false,incomingPort := 0})
  lift (socketReinit none none)
  remove
  finish

def destructFinishPrefix : WGPrefix LifetimeEvent Unit := do
  let d ← liftWGPrefix getDev
  if !d.sendWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
      || !d.decryptQueue.empty || !d.clearWorkQueue.isEmpty then
    liftWGPrefix (unsupported "wg_destruct with queued work (destroy_workqueue runs it)")
  if !d.handshakeQueue.empty then
    liftWGPrefix (invariant "wg_destruct with handshake messages queued (wg_stop drains the ring)")
  liftWGPrefix mayHaveSlept
  liftWGPrefix (modifyDev fun d => {d with handshakeQueueLen := 0})
  liftWGPrefix mayHaveSlept
  liftWGPrefix ratelimiterUninit
  dropDevicePrefix
  liftWGPrefix retireDeviceUnits

theorem wgDestructPrefix_factor : wgDestructPrefix =
    destructWith (fun {_} a => liftWGPrefix a) peerRemoveAllPrefix destructFinishPrefix := rfl

theorem wgDestructObserved_factor : wgDestructObserved =
    destructWith (fun {_} a => liftWGPrefix a) peerRemoveAllObserved
      (liftWGPrefix (pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish)) := rfl

theorem wgDestruct_factor : WG.wgDestruct =
    destructWith (fun {_} a => a) WG.peerRemoveAll
      (pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish) := rfl

theorem destructFinishPrefix_erases : ErasesStatePrefix destructFinishPrefix
    (pinned_const _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish) := by
  unfold destructFinishPrefix
  index_unfold _private.Leanux.Proofs.WG.Configuration.LifecycleCompletion.«0».Leanux.Proofs.WG.Configuration.destructFinish
  repeat' first
    | (maintenance_head dropDevicePrefix; exact dropDevicePrefix_erases)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | with_reducible apply erasesStatePrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

theorem destructFinishPrefix_appends : StateAppends destructFinishPrefix := by
  have drop : StateAppends dropDevicePrefix := fun _ _ _ => ⟨_,rfl⟩
  unfold destructFinishPrefix
  repeat' first
    | with_reducible exact drop
    | exact StateAppends.lift _
    | exact StateAppends.pure _
    | with_reducible apply StateAppends.bind
    | (maintenance_intro; try dsimp only)
    | split

theorem wgDestructPrefix_appends : StateAppends wgDestructPrefix := by
  rw [wgDestructPrefix_factor]
  unfold destructWith
  exact (StateAppends.lift _).bind (fun _ => (StateAppends.lift _).bind (fun _ =>
    Queues.RoutingJoint.peerRemoveAllPrefix_appends.bind (fun _ => destructFinishPrefix_appends)))

end Leanux.Proofs.WG.Configuration

namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Configuration AllowedIps

private theorem nativeRx_lift (a : WG.M α) :
    nativeRx (liftWGPrefix a) = liftWGPrefix a := by
  unfold nativeRx
  rw [← (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_lift)
    AuditEvent.lifetime AuditEvent.lifetime? a |>.2]
  exact ((pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_lift)
    RxHistory.Event.audit RxHistory.auditEvent a).2.symm

private theorem nativeRx_bind {a : WGPrefix LifetimeEvent α} {b : α → WGPrefix LifetimeEvent β}
    (ha : StateAppends a) (hb : ∀ x, StateAppends (b x)) :
    nativeRx a >>= (fun x => nativeRx (b x)) = nativeRx (a >>= b) := by
  have inner := (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_bind)
    AuditEvent.lifetime AuditEvent.lifetime? (fun _ => rfl) ⟨ha,rfl⟩ (fun x => ⟨hb x,rfl⟩)
  have outer := (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.focused_bind)
    RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    ⟨StateAppends.focus AuditEvent.lifetime AuditEvent.lifetime? a,rfl⟩
    (fun x => ⟨StateAppends.focus AuditEvent.lifetime AuditEvent.lifetime? (b x),rfl⟩)
  exact outer.2.trans (congrArg (focusStatePrefix RxHistory.Event.audit RxHistory.auditEvent) inner.2)

private theorem destruct_projects {E F : Type} (ρ : E → Option F)
    {remove finish : WGPrefix E Unit} {lowerRemove lowerFinish : WGPrefix F Unit}
    (hr : StateProjectsPrefix ρ id remove lowerRemove)
    (hf : StateProjectsPrefix ρ id finish lowerFinish) :
    StateProjectsPrefix ρ id (destructWith (fun {_} a => liftWGPrefix a) remove finish)
      (destructWith (fun {_} a => liftWGPrefix a) lowerRemove lowerFinish) := by
  unfold destructWith
  apply StateProjectsPrefix.bind ρ id id
    ((pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) ρ _)
  intro _
  apply StateProjectsPrefix.bind ρ id id
    ((pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) ρ _)
  intro _
  exact StateProjectsPrefix.bind ρ id id hr (fun _ => hf)

private theorem destruct_rx_eq :
    destructWith (fun {_} a => liftWGPrefix a) (nativeRx peerRemoveAllPrefix)
      (nativeRx destructFinishPrefix) = nativeRx wgDestructPrefix := by
  rw [wgDestructPrefix_factor]
  unfold destructWith
  have tail := nativeRx_bind peerRemoveAllPrefix_appends (fun _ => destructFinishPrefix_appends)
  have middle := nativeRx_bind (StateAppends.lift (socketReinit none none))
    (fun _ => peerRemoveAllPrefix_appends.bind (fun _ => destructFinishPrefix_appends))
  have outer := nativeRx_bind (StateAppends.lift (modifyDev fun d => {d with creatingNet := false,incomingPort := 0}))
    (fun _ => (StateAppends.lift (socketReinit none none)).bind
      (fun _ => peerRemoveAllPrefix_appends.bind (fun _ => destructFinishPrefix_appends)))
  dsimp only at outer middle tail ⊢
  simp only [liftWGPrefix] at outer middle tail ⊢
  rw [← outer,← middle,← tail]
  change (liftWGPrefix _ >>= _) = (nativeRx (liftWGPrefix _) >>= _)
  rw [nativeRx_lift]
  congr 1
  funext _
  change (liftWGPrefix _ >>= _) = (nativeRx (liftWGPrefix _) >>= _)
  rw [nativeRx_lift]

def destructDevice : WGPrefix Event Unit :=
  destructWith (fun {_} a => liftWGPrefix a) removeAllPeers (access destructFinishPrefix)

theorem destructDevice_routing : StateProjectsPrefix routingEvent id destructDevice wgDestructObserved := by
  rw [wgDestructObserved_factor]
  exact destruct_projects routingEvent removeAllPeers_routing
    ((pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_erases_frame)
      routingEvent (access_erases destructFinishPrefix_erases) (access_routing _))

theorem destructDevice_rx : StateProjectsPrefix rxEvent id destructDevice (nativeRx wgDestructPrefix) := by
  rw [← destruct_rx_eq]
  exact destruct_projects rxEvent removeAllPeers_rx (access_rx _)

theorem destructDevice_rx_product : ProjectsPrefix rxEvent id (liftWGObserver destructDevice)
    (RxHistory.mixed (liftWGObserver wgDestructPrefix)) := by
  rw [← nativeRx_product]
  exact destructDevice_rx.liftWGObserver _ _

theorem destructDevice_erases : ErasesStatePrefix destructDevice WG.wgDestruct := by
  intro w ambient h
  have hp := congrArg Prod.fst (destructDevice_routing w ambient h)
  have he := wgDestructObserved_erases w ambient (h.filterMap routingEvent)
  have same := hp.symm.trans he
  change ((runWGPrefix destructDevice w ambient h).1.map (fun ((x,v),a) => ((x,v),a))) = _ at same
  change (runWGPrefix destructDevice w ambient h).1 = _
  cases hr : (runWGPrefix destructDevice w ambient h).1 <;> simpa only [hr,Except.map] using same

end Leanux.Proofs.WG.Queues.RoutingJoint
