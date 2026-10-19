import Leanux.Proofs.WG.TransmitSecurity.DriverStagingProjection

namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open HandshakeSecurity.Confirmation.Poll
variable {E F : Type} {ρ : E → Option F} {g : Hooks E} {a : Hooks F}
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem normalList (cb : List (List UInt8) → PrefixM E Unit)
    (ca : List (List UInt8) → PrefixM F Unit)
    (hc : ∀ ps, ProjectsPrefix ρ id (cb ps) (ca ps)) (gro : GroState) :
    ProjectsPrefix ρ id (groNormalListPrefix cb gro) (groNormalListPrefix ca gro) := by
  unfold groNormalListPrefix
  repeat' first | exact hc _ | driver_product_step ρ

private theorem normalOne (cb : List (List UInt8) → PrefixM E Unit)
    (ca : List (List UInt8) → PrefixM F Unit)
    (hc : ∀ ps, ProjectsPrefix ρ id (cb ps) (ca ps)) (gro : GroState) (pkt : List UInt8) (segs : Nat) :
    ProjectsPrefix ρ id (groNormalOnePrefix cb gro pkt segs) (groNormalOnePrefix ca gro pkt segs) := by
  unfold groNormalOnePrefix
  repeat' first
    | (maintenance_head groNormalListPrefix; exact normalList cb ca hc _)
    | driver_product_step ρ

private theorem groReceive (cb : List (List UInt8) → PrefixM E Unit)
    (ca : List (List UInt8) → PrefixM F Unit)
    (hc : ∀ ps, ProjectsPrefix ρ id (cb ps) (ca ps)) (gro : GroState) (pkt : List UInt8) :
    ProjectsPrefix ρ id (napiGroReceivePrefix cb gro pkt) (napiGroReceivePrefix ca gro pkt) := by
  unfold napiGroReceivePrefix
  repeat' first
    | (maintenance_head groNormalOnePrefix; exact normalOne cb ca hc _ _ _)
    | driver_product_step ρ

private theorem groFlush (cb : List (List UInt8) → PrefixM E Unit)
    (ca : List (List UInt8) → PrefixM F Unit)
    (hc : ∀ ps, ProjectsPrefix ρ id (cb ps) (ca ps)) (gro : GroState) :
    ProjectsPrefix ρ id (napiGroFlushAllPrefix cb gro) (napiGroFlushAllPrefix ca gro) := by
  unfold napiGroFlushAllPrefix
  repeat' first
    | (maintenance_head groNormalOnePrefix; exact normalOne cb ca hc _ _ _)
    | (maintenance_head groNormalListPrefix; exact normalList cb ca hc _)
    | driver_product_step ρ

theorem poll_projects (h : HooksProjects ρ g a) (pid : PeerId) (budget : Nat)
    (cb : List (List UInt8) → PrefixM E Unit) (ca : List (List UInt8) → PrefixM F Unit)
    (hc : ∀ ps, ProjectsPrefix ρ id (cb ps) (ca ps)) :
    ProjectsPrefix ρ id (pollObserved g pid budget cb) (pollObserved a pid budget ca) := by
  obtain ⟨scopeMap,enter,leave,_⟩ := h.candidate
  exact AuthenticatedEffects.CandidatePoll.projects ρ scopeMap _ _ _ _ _ _ _ _ _ _ _ _ _ _
    enter leave (fun _ => (Projection.state_lift ρ _).liftWGObserver ρ id)
    h.counterCheck (fun peer pkt ep => (consume_projects h peer pkt ep).liftWGObserver ρ id)
    (groReceive cb ca hc) (groFlush cb ca hc) pid budget

private theorem reply_projects (h : HooksProjects ρ g a) (dst : Nat) (bytes : List UInt8) :
    ProjectsPrefix ρ id
      (reply4With (fun family addr packets mtu => liftWGObserver (transmitObserved g family addr packets mtu)) dst bytes)
      (reply4With (fun family addr packets mtu => liftWGObserver (transmitObserved a family addr packets mtu)) dst bytes) := by
  unfold reply4With
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (maintenance_head transmitObserved; exact (transmit_projects h _ _ _ _).liftWGObserver ρ id)
    | driver_product_step ρ

private theorem receive4_projects (h : HooksProjects ρ g a) (bytes : List UInt8) :
    ProjectsPrefix ρ id
      (receive4With (reply4With (fun family addr packets mtu => liftWGObserver (transmitObserved g family addr packets mtu))) bytes)
      (receive4With (reply4With (fun family addr packets mtu => liftWGObserver (transmitObserved a family addr packets mtu))) bytes) :=
  receive4With_projects ρ _ _ (reply_projects h) bytes

theorem stack_projects (h : HooksProjects ρ g a) (bytes : List UInt8) :
    ProjectsPrefix ρ id (stackObserved g bytes) (stackObserved a bytes) := by
  unfold stackObserved stackReceiveWith
  repeat' first
    | (maintenance_head receive4With; exact receive4_projects h _)
    | driver_product_step ρ

theorem flush_projects (h : HooksProjects ρ g a) (ps : List (List UInt8)) :
    ProjectsPrefix ρ id (stackFlushObserved g ps) (stackFlushObserved a ps) := by
  induction ps with
  | nil => exact projectsPrefix_pure ρ id _
  | cons p ps ih =>
    simp only [stackFlushObserved,List.forM_eq_forM,List.forM_cons] at ih ⊢
    exact projectsPrefix_bind ρ id id (stack_projects h p) (fun _ => ih)

theorem nativePoll_projects (h : HooksProjects ρ g a) (pid : PeerId) (budget : Nat) :
    ProjectsPrefix ρ id (nativePollObserved g pid budget) (nativePollObserved a pid budget) :=
by
  obtain ⟨scopeMap,enter,leave,stackInput⟩ := h.candidate
  have callback := AuthenticatedEffects.GroOccurrence.stack_matching ρ scopeMap
    g.stackInput a.stackInput (stackObserved g) (stackObserved a) (stack_projects h) stackInput
  exact RetirementSecurity.NestedPeerRelease.poll_projects ρ scopeMap
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ enter leave
    (fun _ => (Projection.state_lift ρ _).liftWGObserver ρ id)
    (fun peer => (h.peerRelease peer).liftWGObserver ρ id)
    h.counterCheck (fun peer pkt ep => (consume_projects h peer pkt ep).liftWGObserver ρ id)
    (AuthenticatedEffects.GroOccurrence.receive_matching ρ scopeMap _ _ callback)
    (AuthenticatedEffects.GroOccurrence.flushAll_matching ρ scopeMap _ _ callback) pid budget

theorem softirq_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (softirqObserved g) (softirqObserved a) := by
  unfold softirqObserved RxNapi.softirqWith runWorkerPrefix
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (maintenance_head nativePollObserved; exact nativePoll_projects h _ _)
    | (maintenance_head liftWGPrefix; exact (Projection.state_lift ρ _).liftWGObserver ρ id)
    | driver_product_step ρ

theorem inline_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (inlinePollObserved g) (inlinePollObserved a) := by
  unfold inlinePollObserved RxNapi.inlineWith
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (maintenance_head nativePollObserved; exact nativePoll_projects h _ _)
    | (maintenance_head liftWGPrefix; exact (Projection.state_lift ρ _).liftWGObserver ρ id)
    | driver_product_step ρ

theorem irqExit_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (irqExitObserved g) (irqExitObserved a) := by
  unfold irqExitObserved RxNapi.irqExitWith
  repeat' first
    | (maintenance_head softirqObserved; exact softirq_projects h)
    | (maintenance_head liftWGPrefix; exact (Projection.state_lift ρ _).liftWGObserver ρ id)
    | driver_product_step ρ

end Leanux.Proofs.WG.TransmitSecurity.Driver
