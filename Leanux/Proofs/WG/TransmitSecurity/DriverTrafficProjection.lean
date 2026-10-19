import Leanux.Proofs.WG.TransmitSecurity.DriverDeferredProjection

namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
variable {E F : Type} {ρ : E → Option F} {g : Hooks E} {a : Hooks F}
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem inject_projects (h : HooksProjects ρ g a) (family port : Nat)
    (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProjectsPrefix ρ id (injectObserved g family port msg tos ll dest)
      (injectObserved a family port msg tos ll dest) :=
  TrafficSource.inject_projects ρ _ _ _ _ _ _ (fun _ _ => projectsPrefix_lift ρ _)
    (crypt_projects h) (fun _ _ => projectsPrefix_lift ρ _) _ _ _ _ _ _

theorem afterBatch_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (afterBatchObserved g) (afterBatchObserved a) :=
  AuthenticatedEffects.DeliverySource.afterBatch_projects ρ _ _ _ _ _ _ _ _ _ _ (crypt_projects h)
    (sendWorkers_projects h) (sendWorker_projects h) (schedule_projects h)
    (fun _ _ => projectsPrefix_lift ρ _) _ _ h.deliver

theorem flood_projects (h : HooksProjects ρ g a) (count port family : Nat)
    (messages : List (List UInt8)) :
    ProjectsPrefix ρ id (floodObserved g count port family messages)
      (floodObserved a count port family messages) :=
  TrafficSource.flood_projects ρ _ _ _ _ _ _ _ _ (fun _ _ => projectsPrefix_lift ρ _)
    (inline_projects h) (afterBatch_projects h) (fun _ _ => projectsPrefix_lift ρ _) _ _ _ _

theorem batchItem_projects (h : HooksProjects ρ g a) (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    ProjectsPrefix ρ id (batchItemObserved g d cqes item) (batchItemObserved a d cqes item) :=
  batchItemWith_projects ρ _ _ _ _ _ _ _ _ (fun _ _ => projectsPrefix_lift ρ _)
    (inline_projects h) (fun _ _ => projectsPrefix_lift ρ _)
    (fun family addr packets mtu => (fixture_projects h _ _ _ (transmit_projects h family addr packets mtu)).liftWGObserver ρ id) d cqes item

theorem batch_projects (h : HooksProjects ρ g a) (items : List Env.BatchItem) :
    ProjectsPrefix ρ id (batchObserved g items) (batchObserved a items) := by
  unfold batchObserved TrafficSource.batchWith
  repeat' first
    | (maintenance_head batchItemObserved; exact batchItem_projects h _ _ _)
    | (maintenance_head afterBatchObserved; exact afterBatch_projects h)
    | driver_product_step ρ

theorem syscallXmit_projects (h : HooksProjects ρ g a) (family addr : Nat)
    (payload : List UInt8) (opts : Env.XmitOpts) :
    ProjectsPrefix ρ id (syscallXmitObserved g family addr payload opts)
      (syscallXmitObserved a family addr payload opts) :=
  syscallXmitWith_projects ρ _ _ _ _ (fun _ _ => projectsPrefix_lift ρ _)
    (fun family addr packets mtu => (fixture_projects h _ _ _ (transmit_projects h family addr packets mtu)).liftWGObserver ρ id) _ _ _ _

end Leanux.Proofs.WG.TransmitSecurity.Driver
