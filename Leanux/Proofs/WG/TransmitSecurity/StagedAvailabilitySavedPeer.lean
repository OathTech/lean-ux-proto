import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableSavedPeer
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityEffects

/-! The observed getter retains the native peer-slot evidence needed by a
later saved metadata write. Native store frames carry it across guard reads. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.SavedPeer
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects.CausalJournal

def Saved (pid : PeerId) (p : Peer) (h : List Event) (w : WGWorld) : Prop :=
  Carrier h w ∧ stagedAt w pid = some (p.internalId,p.staged)

theorem read (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => Carrier h w) Safe (liftWGPrefix (getPeer pid))
      (fun p h w _ => Saved pid p h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before => before.2)
  intro h w a p v b before run
  have kept := (hoare_iff_run_ambient _ _ _).mp (Native.read_saved_peer pid)
    w a p v b before.1 run
  exact ⟨⟨kept.1,before.2⟩,kept.2⟩

theorem store (pid : PeerId) (p : Peer) (action : WG.M α) (same : SameWGStore action) :
    StatePrefixPreserves (fun h w _ => Saved pid p h w) Safe (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before => before.1.2)
  intro h w a value v b before run
  have kept := (hoare_iff_run_ambient _ _ _).mp (Native.saved_peer_store pid p action same)
    w a value v b ⟨before.1.1,before.2⟩ run
  exact ⟨⟨kept.1,before.1.2⟩,kept.2⟩

theorem write (pid : PeerId) (p : Peer) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged) :
    StatePrefixEnsures (fun h w _ => Saved pid p h w) Safe (liftWGPrefix (setPeer pid (f p)))
      (fun _ h w _ => Carrier h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before => before.1.2)
  intro h w a value v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (Native.write_saved_peer pid p f same)
    w a value v b ⟨before.1.1,before.2⟩ run,before.1.2⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.SavedPeer
