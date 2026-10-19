import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveStaging

namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive.Saved
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

def Saved (pid : PeerId) (p : Peer) (h : List TimestampReceipt) (w : WGWorld) : Prop :=
  StateInv h w ∧ Responder.SavedNativePeer pid p w

theorem read_saved (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => StateInv h w) History (liftWGPrefix (getPeer pid))
      (fun p h w _ => Saved pid p h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
  intro h w a p v b hi run
  obtain ⟨carried,saved⟩ := (hoare_iff_run_ambient _ _ _).mp (TimestampArchive.read_saved pid h)
    _ _ _ _ _ hi run
  exact ⟨carried,saved⟩

theorem saved_ambient (pid : PeerId) (p : Peer) (a : AmbientM α) :
    StatePrefixPreserves (fun h w _ => Saved pid p h w) History (liftWGPrefix (monadLift a)) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.1)
  intro h w b x v c hi run
  exact (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient a (Saved pid p h)) _ _ _ _ _ hi run

theorem saved_store (pid : PeerId) (p : Peer) (a : WG.M α) (frame : SameWGStore a) :
    StatePrefixPreserves (fun h w _ => Saved pid p h w) History (liftWGPrefix a) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.1)
  intro h w b x v c hi run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp frame w b x v c run
  have device : v.dev = w.dev := congrArg WGStoreView.dev same
  refine ⟨(hoare_iff_run_ambient _ _ _).mp (frame_store h _ frame)
    _ _ _ _ _ hi.1 run,?_⟩
  obtain ⟨d,hd,hp⟩ := hi.2
  exact ⟨d,device.trans hd,hp⟩

theorem write_saved (pid : PeerId) (p : Peer) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).latestTimestamp = p.latestTimestamp) :
    StatePrefixEnsures (fun h w _ => Saved pid p h w) History (liftWGPrefix (setPeer pid (f p)))
      (fun _ h w _ => StateInv h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1.1)
  intro h w a result v b hi run
  exact (hoare_iff_run_ambient _ _ _).mp (TimestampArchive.write_saved pid p f same h)
    _ _ _ _ _ hi run

theorem forget_saved (pid : PeerId) (p : Peer) {action : WGPrefix TimestampReceipt α}
    (checked : Preserves action) :
    StatePrefixEnsures (fun h w _ => Saved pid p h w) History action (fun _ h w _ => StateInv h w) :=
  checked.consequence (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive.Saved
