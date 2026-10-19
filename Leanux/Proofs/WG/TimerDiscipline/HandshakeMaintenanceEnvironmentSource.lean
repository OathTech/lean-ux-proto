import Leanux.Proofs.WG.TimerDiscipline.HandshakeMaintenanceControlSource
import Leanux.Proofs.WG.Noise.DriverTagEnvironmentSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeMaintenance
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open HandshakeJournal

def envDown : PrefixM Event Int :=
  Noise.DriverTags.Environment.envDownWith (fun {_} a => liftPrefix a)
    (liftPrefix Env.requireIdleDevice) (liftWGObserver down)
def envDelete : PrefixM Event Int :=
  Configuration.envDeleteWith (fun {_} a => liftPrefix a)
    (liftPrefix Env.requireIdleDevice) (liftWGObserver down) (liftWGObserver destruct)

theorem envDown_erases : ErasesPrefix envDown Env.wgDown := by
  rw [Noise.DriverTags.Environment.envDown_factor]
  unfold envDown Noise.DriverTags.Environment.envDownWith
  repeat' first
    | with_reducible exact liftWGObserver_erases down_erases
    | exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

theorem envDelete_erases : ErasesPrefix envDelete Env.wgDelete := by
  rw [Configuration.envDelete_factor]
  unfold envDelete Configuration.envDeleteWith
  repeat' first
    | with_reducible exact liftWGObserver_erases down_erases
    | with_reducible exact liftWGObserver_erases destruct_erases
    | exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

theorem quiet_product_preserves {α : Type} (S : List Event → Prop) (a : Leanux.M α) :
    PrefixPreserves (fun h _ => S h) S (liftPrefix a) :=
  PrefixEnsures.preserves (PrefixEnsures.lift _ (fun _ _ h => h) (fun _ _ _ _ h _ => h))

theorem envDown_preserves (S : List Event → Prop)
    (hs : ∀ pid, StatePrefixPreserves (fun h _ _ => S h) S (sendWorker pid)) :
    PrefixPreserves (fun h _ => S h) S envDown := by
  unfold envDown Noise.DriverTags.Environment.envDownWith
  repeat' first
    | (poll_preserve_head liftWGObserver; exact (down_preserves S hs).liftWGObserver.preserves)
    | with_reducible exact quiet_product_preserves S _
    | with_reducible exact PrefixPreserves.pure (I := fun h _ => S h) (S := S) (fun _ _ h => h) _
    | (poll_preserve_head Bind.bind; apply PrefixPreserves.bind)
    | maintenance_intro
    | rx_phase_reduce
    | split

theorem envDelete_preserves (S : List Event → Prop)
    (hs : ∀ pid, StatePrefixPreserves (fun h _ _ => S h) S (sendWorker pid)) :
    PrefixPreserves (fun h _ => S h) S envDelete := by
  unfold envDelete Configuration.envDeleteWith
  repeat' first
    | (poll_preserve_head liftWGObserver; first
        | exact (down_preserves S hs).liftWGObserver.preserves
        | exact (destruct_preserves S hs).liftWGObserver.preserves)
    | with_reducible exact quiet_product_preserves S _
    | with_reducible exact PrefixPreserves.pure (I := fun h _ => S h) (S := S) (fun _ _ h => h) _
    | (poll_preserve_head Bind.bind; apply PrefixPreserves.bind)
    | maintenance_intro
    | rx_phase_reduce
    | split

theorem envDown_valid :
    PrefixPreserves (fun h _ => ValidHistory h) ValidHistory envDown :=
  envDown_preserves ValidHistory sendWorker_valid

theorem envDown_paired :
    PrefixPreserves (fun h _ => Paired h) Paired envDown :=
  envDown_preserves Paired sendWorker_paired

theorem envDown_appends : Appends envDown := by
  intro w h
  obtain ⟨more,same,_,_⟩ := envDown_preserves (fun _ => True)
    (fun p => appends_true _ (sendWorker_appends p)) w h True.intro
  exact ⟨more,same⟩

theorem envDelete_valid :
    PrefixPreserves (fun h _ => ValidHistory h) ValidHistory envDelete :=
  envDelete_preserves ValidHistory sendWorker_valid

theorem envDelete_paired :
    PrefixPreserves (fun h _ => Paired h) Paired envDelete :=
  envDelete_preserves Paired sendWorker_paired

theorem envDelete_appends : Appends envDelete := by
  intro w h
  obtain ⟨more,same,_,_⟩ := envDelete_preserves (fun _ => True)
    (fun p => appends_true _ (sendWorker_appends p)) w h True.intro
  exact ⟨more,same⟩
end Leanux.Proofs.WG.TimerDiscipline.HandshakeMaintenance
