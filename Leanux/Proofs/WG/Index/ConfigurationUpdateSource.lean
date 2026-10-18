import Leanux.Proofs.WG.Index.ConfigurationIndexFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Lifetimes Std.Do
open Leanux.Proofs.WG.Configuration

theorem peerReadUpdate_preserves {α : Type} (P : WGWorld → Prop)
    (pid : PeerId) (f : Peer → Peer) (middle : Peer → WG.M α)
    (same : ∀p, SameView (id : WGWorld → WGWorld) (middle p))
    (update : Preserves P (getPeer pid >>= fun p=>setPeer pid (f p))) :
    Preserves P (do let p ← getPeer pid
                    let x ← middle p
                    setPeer pid (f p)
                    pure x) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,read,run⟩ := run
  obtain ⟨sameRead,sameTime,d,device,resident⟩ := getPeer_normal pid w u p a c read
  subst u
  subst c
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨x,u,c,between,run⟩ := run
  have equality := (ProjectedAction.iff_run_ambient _ _ _).mp (same p) w a x u c between
  change u=w at equality
  subst u
  simp [setPeer,modifyDev,device] at run
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
  apply (hoare_iff_run_ambient _ _ _).mp update w a () _ a pre
  simp [getPeer,getDev,device,resident,setPeer,modifyDev]

end Leanux.Proofs.WG.Index.ConfigurationIndex
