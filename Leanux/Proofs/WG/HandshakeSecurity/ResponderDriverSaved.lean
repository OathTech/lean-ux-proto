import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverStaging

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

def Saved (pid : PeerId) (p : Peer) (h : List Event) (w : WGWorld) : Prop :=
  Inv h w ∧ SavedNativePeer pid p w

theorem read_saved (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => Inv h w) Safe (liftWGPrefix (getPeer pid))
      (fun p h w _ => Saved pid p h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.2)
  intro h w a p v b hi run
  obtain ⟨carried,saved⟩ := (hoare_iff_run_ambient _ _ _).mp (carrier_read pid (labels h))
    _ _ _ _ _ hi.1 run
  exact ⟨⟨carried,hi.2⟩,saved⟩

theorem saved_ambient (pid : PeerId) (p : Peer) (a : AmbientM α) :
    StatePrefixPreserves (fun h w _ => Saved pid p h w) Safe (liftWGPrefix (monadLift a)) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.2)
  intro h w b x v c hi run
  exact (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient a (Saved pid p h)) _ _ _ _ _ hi run

theorem saved_store (pid : PeerId) (p : Peer) (a : WG.M α) (frame : SameWGStore a) :
    StatePrefixPreserves (fun h w _ => Saved pid p h w) Safe (liftWGPrefix a) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.2)
  intro h w b x v c hi run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp frame w b x v c run
  have device : v.dev = w.dev := congrArg WGStoreView.dev same
  refine ⟨⟨(hoare_iff_run_ambient _ _ _).mp (carrier_store frame (labels h))
    _ _ _ _ _ hi.1.1 run,hi.1.2⟩,?_⟩
  obtain ⟨d,hd,hp⟩ := hi.2
  exact ⟨d,device.trans hd,hp⟩

theorem write_saved (pid : PeerId) (p : Peer) (f : Peer → Peer)
    (slots : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p)
    (configured : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p) :
    StatePrefixEnsures (fun h w _ => Saved pid p h w) Safe (liftWGPrefix (setPeer pid (f p)))
      (fun _ h w _ => Inv h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.2)
  intro h w a result v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (carrier_write pid p f slots configured (labels h))
    _ _ _ _ _ ⟨hi.1.1,hi.2⟩ run,hi.1.2⟩

theorem forget_saved (pid : PeerId) (p : Peer) {action : WGPrefix Event α}
    (checked : Preserves action) :
    StatePrefixEnsures (fun h w _ => Saved pid p h w) Safe action (fun _ h w _ => Inv h w) :=
  checked.consequence (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
