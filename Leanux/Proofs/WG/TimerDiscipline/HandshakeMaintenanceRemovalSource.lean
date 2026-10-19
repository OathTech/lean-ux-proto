import Leanux.Proofs.WG.TimerDiscipline.HandshakeMaintenanceFlushSource
import Leanux.Proofs.WG.Noise.DriverTagRemovalSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeMaintenance
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open HandshakeJournal

def afterDead (pid : PeerId) : Obs Unit :=
  Noise.DriverTags.Removal.afterDeadWith (fun {_} a => liftWGPrefix a)
    (fun p => liftWGPrefix (keypairsClear p)) timersStop drain
    (fun p => liftWGPrefix (WG.peerPut (some p))) pid
def remove (peer : Option PeerId) : Obs Unit :=
  Configuration.peerRemoveWith (fun {_} a => liftWGPrefix a)
    (fun p => liftWGPrefix (WG.peerMakeDead p)) afterDead peer
def removeAll : Obs Unit :=
  Configuration.peerRemoveAllWith (fun {_} a => liftWGPrefix a)
    (liftWGPrefix WG.free) (fun p => liftWGPrefix (WG.peerMakeDead p)) afterDead
def destruct : Obs Unit :=
  Configuration.destructWith (fun {_} a => liftWGPrefix a)
    removeAll (liftWGPrefix Noise.DriverTags.Removal.destructFinishSource)

theorem afterDead_erases (pid : PeerId) :
    ErasesStatePrefix (afterDead pid) (WG.peerRemoveAfterDead pid) := by
  rw [Noise.DriverTags.Removal.afterDead_factor]
  unfold afterDead Noise.DriverTags.Removal.afterDeadWith
  repeat' first
    | with_reducible exact timersStop_erases _
    | with_reducible exact drain_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

theorem remove_erases (peer : Option PeerId) :
    ErasesStatePrefix (remove peer) (WG.peerRemove peer) := by
  rw [Configuration.peerRemove_factor]
  unfold remove Configuration.peerRemoveWith
  repeat' first
    | with_reducible exact afterDead_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

theorem removeAll_erases : ErasesStatePrefix removeAll WG.peerRemoveAll := by
  rw [Configuration.peerRemoveAll_factor]
  unfold removeAll Configuration.peerRemoveAllWith
  repeat' first
    | with_reducible exact afterDead_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | (maintenance_intro; try dsimp only)

theorem destruct_erases : ErasesStatePrefix destruct WG.wgDestruct := by
  rw [Configuration.wgDestruct_factor]
  unfold destruct Configuration.destructWith
  exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
    erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
    erasesStatePrefix_bind removeAll_erases (fun _ => erasesStatePrefix_lift _)))

theorem afterDead_preserves (S : List Event → Prop)
    (hs : ∀ pid, StatePrefixPreserves (fun h _ _ => S h) S (sendWorker pid)) (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => S h) S (afterDead pid) := by
  change StatePrefixEnsures _ _ _ (fun _ h _ _ => S h)
  unfold afterDead Noise.DriverTags.Removal.afterDeadWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head timersStop; exact timersStop_preserves S hs _)
    | (maintenance_head drain; exact drain_preserves S hs _)
    | (maintenance_head liftWGPrefix; exact quiet_preserves S _)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun _ _ _ h => h) (fun _ _ _ h => h))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h _ _ => S h))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_intro
    | split

theorem remove_preserves (S : List Event → Prop)
    (hs : ∀ pid, StatePrefixPreserves (fun h _ _ => S h) S (sendWorker pid)) (peer : Option PeerId) :
    StatePrefixPreserves (fun h _ _ => S h) S (remove peer) := by
  change StatePrefixEnsures _ _ _ (fun _ h _ _ => S h)
  unfold remove Configuration.peerRemoveWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head afterDead; exact afterDead_preserves S hs _)
    | (maintenance_head liftWGPrefix; exact quiet_preserves S _)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun _ _ _ h => h) (fun _ _ _ h => h))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h _ _ => S h))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_intro
    | split

theorem removeAll_preserves (S : List Event → Prop)
    (hs : ∀ pid, StatePrefixPreserves (fun h _ _ => S h) S (sendWorker pid)) :
    StatePrefixPreserves (fun h _ _ => S h) S removeAll := by
  change StatePrefixEnsures _ _ _ (fun _ h _ _ => S h)
  unfold removeAll Configuration.peerRemoveAllWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | (maintenance_head afterDead; exact afterDead_preserves S hs _)
    | (maintenance_head liftWGPrefix; exact quiet_preserves S _)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun _ _ _ h => h) (fun _ _ _ h => h))
    | (maintenance_head ForIn.forIn
       apply Noise.DriverTags.Flush.list_preserves (fun h _ _ => S h) S (fun _ _ _ h => h)
       intro loopPeer loopState
       change StatePrefixEnsures _ _ _ (fun _ h _ _ => S h))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h _ _ => S h))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_intro

theorem destruct_preserves (S : List Event → Prop)
    (hs : ∀ pid, StatePrefixPreserves (fun h _ _ => S h) S (sendWorker pid)) :
    StatePrefixPreserves (fun h _ _ => S h) S destruct := by
  unfold destruct Configuration.destructWith
  exact (quiet_preserves S _).bind (fun _ =>
    (quiet_preserves S _).bind (fun _ =>
    (removeAll_preserves S hs).bind (fun _ => quiet_preserves S _)))

theorem afterDead_valid (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (afterDead pid) :=
  afterDead_preserves ValidHistory sendWorker_valid pid

theorem afterDead_paired (pid : PeerId) :
    StatePrefixPreserves (fun h _ _ => Paired h) Paired (afterDead pid) :=
  afterDead_preserves Paired sendWorker_paired pid

theorem afterDead_appends (pid : PeerId) : StateAppends (afterDead pid) :=
  true_appends _ (afterDead_preserves (fun _ => True)
    (fun p => appends_true _ (sendWorker_appends p)) pid)

theorem remove_valid (peer : Option PeerId) :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory (remove peer) :=
  remove_preserves ValidHistory sendWorker_valid peer

theorem remove_paired (peer : Option PeerId) :
    StatePrefixPreserves (fun h _ _ => Paired h) Paired (remove peer) :=
  remove_preserves Paired sendWorker_paired peer

theorem remove_appends (peer : Option PeerId) : StateAppends (remove peer) :=
  true_appends _ (remove_preserves (fun _ => True)
    (fun p => appends_true _ (sendWorker_appends p)) peer)

theorem removeAll_valid :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory removeAll :=
  removeAll_preserves ValidHistory sendWorker_valid 

theorem removeAll_paired :
    StatePrefixPreserves (fun h _ _ => Paired h) Paired removeAll :=
  removeAll_preserves Paired sendWorker_paired 

theorem removeAll_appends : StateAppends removeAll :=
  true_appends _ (removeAll_preserves (fun _ => True)
    (fun p => appends_true _ (sendWorker_appends p)) )

theorem destruct_valid :
    StatePrefixPreserves (fun h _ _ => ValidHistory h) ValidHistory destruct :=
  destruct_preserves ValidHistory sendWorker_valid 

theorem destruct_paired :
    StatePrefixPreserves (fun h _ _ => Paired h) Paired destruct :=
  destruct_preserves Paired sendWorker_paired 

theorem destruct_appends : StateAppends destruct :=
  true_appends _ (destruct_preserves (fun _ => True)
    (fun p => appends_true _ (sendWorker_appends p)) )
end Leanux.Proofs.WG.TimerDiscipline.HandshakeMaintenance
