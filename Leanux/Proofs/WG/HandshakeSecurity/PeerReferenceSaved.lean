import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceHistory

/-! Source-local saved records carry their positive count, without claiming
that later writes retain the same resident allocation. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference.Saved
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def Saved (p : Peer) (h : List Exchange.Event) (w : WGWorld) : Prop := StateInv h w ∧ 0 < p.refcount

theorem read_saved (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => StateInv h w) Safe (liftWGPrefix (getPeer pid))
      (fun p h w _ => Saved p h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before => before.1)
  intro h w a p v b before run
  obtain ⟨positive,count⟩ := (hoare_iff_run_ambient _ _ _).mp (PeerReference.read_saved pid)
    w a p v b before.2 run
  exact ⟨⟨before.1,positive⟩,count⟩

theorem saved_store (p : Peer) (action : WG.M α) (same : SameWGStore action) :
    StatePrefixPreserves (fun h w _ => Saved p h w) Safe (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before => before.1.1)
  intro h w a value v b before run
  exact ⟨⟨before.1.1,(hoare_iff_run_ambient _ _ _).mp
    (PeerReference.store same) w a value v b before.1.2 run⟩,before.2⟩

theorem write_saved (pid : PeerId) (p : Peer) (f : Peer → Peer)
    (same : ∀ p, (f p).refcount = p.refcount) :
    StatePrefixEnsures (fun h w _ => Saved p h w) Safe (liftWGPrefix (setPeer pid (f p)))
      (fun _ h w _ => StateInv h w) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before => before.1.1)
  intro h w a result v b before run
  exact ⟨before.1.1,(hoare_iff_run_ambient _ _ _).mp
    (PeerReference.write_saved pid p f same) w a result v b ⟨before.1.2,before.2⟩ run⟩

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference.Saved
