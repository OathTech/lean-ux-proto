import Leanux.Proofs.WG.Noise.DriverTagEnvironmentFactors
import Leanux.Proofs.WG.Noise.DriverTagEnvironmentFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Environment
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

/-! Source: up, creation and namespace cleanup are tag-silent. Down and
deletion execute the actual receipt-bearing stop and destruction observers. -/
universe u

def upObserved : ProductObs Int := discard envWgUpAudit
def createObserved : ProductObs Int := discard (liftWGObserver wgCreatePrefix)
def preexitObserved : ProductObs Unit := discard (liftWGObserver netnsPreExitPrefix)
def cleanupObserved : ProductObs Unit := discard envNetnsCleanupAudit

def downObserved : ProductObs Int :=
  envDownWith (fun {_} a => liftPrefix a) (liftPrefix Env.requireIdleDevice)
    (liftWGObserver Control.downObserved)

def deleteObserved : ProductObs Int :=
  Leanux.Proofs.WG.Configuration.envDeleteWith (fun {_} a => liftPrefix a)
    (liftPrefix Env.requireIdleDevice) (liftWGObserver Control.downObserved)
    (liftWGObserver Removal.destructObserved)

theorem upObserved_erases : ErasesPrefix upObserved Env.wgUp :=
  discard_erases _ _ envWgUpAudit_erases

theorem createObserved_erases : ErasesPrefix createObserved (liftWG WG.wgCreate) :=
  discard_erases _ _ (liftWGObserver_erases wgCreatePrefix_erases)

theorem preexitObserved_erases : ErasesPrefix preexitObserved (liftWG netnsPreExit) :=
  discard_erases _ _ (liftWGObserver_erases netnsPreExitPrefix_erases)

theorem cleanupObserved_erases : ErasesPrefix cleanupObserved Env.netnsCleanup :=
  discard_erases _ _ envNetnsCleanupAudit_erases

theorem downObserved_erases : ErasesPrefix downObserved Env.wgDown := by
  rw [envDown_factor]
  unfold downObserved envDownWith
  repeat' first
    | with_reducible exact liftWGObserver_erases Control.downObserved_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

theorem deleteObserved_erases : ErasesPrefix deleteObserved Env.wgDelete := by
  rw [Leanux.Proofs.WG.Configuration.envDelete_factor]
  unfold deleteObserved Leanux.Proofs.WG.Configuration.envDeleteWith
  repeat' first
    | with_reducible exact liftWGObserver_erases Control.downObserved_erases
    | with_reducible exact liftWGObserver_erases Removal.destructObserved_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

theorem upObserved_preserves (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory upObserved := by
  rw [upObserved,discard_eq _ _ envWgUpAudit_erases]
  exact Scheduler.lift_kept entry _ envUp_native

theorem createObserved_preserves (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory createObserved := by
  rw [createObserved,discard_eq _ _ (liftWGObserver_erases wgCreatePrefix_erases)]
  exact Scheduler.lift_kept entry _ (fun initial => lift_native initial _ create_native)

theorem preexitObserved_preserves (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory preexitObserved := by
  rw [preexitObserved,discard_eq _ _ (liftWGObserver_erases netnsPreExitPrefix_erases)]
  exact Scheduler.lift_kept entry _ (fun initial => lift_native initial _ preexit_native)

theorem cleanupObserved_preserves (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory cleanupObserved := by
  rw [cleanupObserved,discard_eq _ _ envNetnsCleanupAudit_erases]
  exact Scheduler.lift_kept entry _ cleanup_native

macro "driver_lifecycle_prefix_step " entry:term : tactic => `(tactic| first
  | (poll_preserve_head liftWGObserver
     first
     | with_reducible exact Scheduler.native_observed $entry _ (Control.downObserved_preserves $entry)
     | with_reducible exact Scheduler.native_observed $entry _ (Removal.destructObserved_preserves $entry))
  | (poll_preserve_head liftPrefix
     first
     | with_reducible exact lift_product_frame $entry (liftWG getDev) (native_product_frame _ (store_frame getDev_sameWGStore))
     | with_reducible exact lift_product_frame $entry (liftWG mayHaveSlept) (native_product_frame _ (store_frame mayHaveSlept_sameWGStore))
     | (apply Scheduler.lift_kept $entry
        intro initial
        first
        | (rx_retention_head Env.requireIdleDevice
           exact Silent.product_store initial _ PendingScheduler.requireIdleDevice_store)
        | driver_lifecycle_env_step initial))
  | (poll_preserve_head Pure.pure; exact PrefixPreserves.pure (safe $entry) _)
  | (poll_preserve_head Bind.bind; apply PrefixPreserves.bind)
  | (poll_preserve_head ite; apply PrefixPreserves.ite)
  | maintenance_intro
  | rx_phase_reduce
  | split)

theorem downObserved_preserves (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory downObserved := by
  unfold downObserved envDownWith
  repeat' driver_lifecycle_prefix_step entry

theorem deleteObserved_preserves (entry : TagMap) :
    PrefixPreserves (StateInv entry) ValidHistory deleteObserved := by
  unfold deleteObserved Leanux.Proofs.WG.Configuration.envDeleteWith
  repeat' driver_lifecycle_prefix_step entry

end Leanux.Proofs.WG.Noise.DriverTags.Environment
