import Leanux.Proofs.WG.Noise.PendingAllowedInsertionFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Std.Do Queues

theorem peerReadUpdate_frame {α : Type} (pid : PeerId) (f : Peer → Peer)
    (middle : Peer → WG.M α)
    (same : ∀ p, SameView (fun w : WGWorld => w) (middle p))
    (next : ∀ p, (f p).keypairNext = p.keypairNext) :
    SameView view (do
      let p ← getPeer pid
      let x ← middle p
      setPeer pid (f p)
      pure x) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v after run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,current,inputs,read,run⟩ := run
  obtain ⟨worldEq,ambientEq,d,device,resident⟩ := Origins.getPeer_return pid w current p ambient inputs read
  subst current
  subst inputs
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨result,middleWorld,middleAmbient,mid,run⟩ := run
  have equality := (ProjectedAction.iff_run_ambient _ _ _).mp (same p) _ _ _ _ _ mid
  change middleWorld = w at equality
  subst middleWorld
  simp [setPeer,modifyDev,device] at run
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
  apply Store.ext
  · rfl
  · funext tracked
    by_cases eq : pid = tracked
    · subst tracked
      simp [view,pending,device,resident,next]
    · simp [view,pending,device,Std.TreeMap.getElem?_insert,eq]

theorem keepaliveUpdate_frame (pid : PeerId) (interval : Nat) (running : Bool) :
    SameView view (do
      let p ← getPeer pid
      let send ← WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
        (WG.andM (branch .peerKeepaliveNonzero (interval != 0)) (branch .peerKeepaliveRunning running))
      setPeer pid {p with persistentKeepaliveInterval := interval}
      pure send) := by
  apply peerReadUpdate_frame pid (fun p => {p with persistentKeepaliveInterval := interval})
  · intro p initial
    change Preserves (fun w : WGWorld => w = initial) _
    unfold WG.andM
    simp (config := {zeta := false}) only [branch]
    repeat' first
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | rx_retention_step
  · intro p; rfl

end Leanux.Proofs.WG.Noise.PendingTickets
