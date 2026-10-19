import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableEffects

/-! A native saved-peer metadata update retains provenance and returns the
actual prior peer value for its continuation. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem update_return (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged) :
    Preserves (Inv h) (do let p ← getPeer pid; setPeer pid (f p); pure p) := by
  apply frame
  · exact PacketOrigins.epoch_ring ((TxRing.getPeer_frame pid).bind (fun p =>
      (TxRing.setPeer_frame pid (f p)).bind (fun _ => SameView.pure _ _)))
  · intro initial
    let P := fun queues : PeerId → Option (Nat × List Packet) =>
      ∀ q value, queues q = some value → stagedAt initial q = some value
    apply hoare_bind _ _ (Staged.read_saved P pid)
    intro peer
    have write := Staged.write_saved P pid (f peer)
    rw [(same peer).1,(same peer).2] at write
    exact hoare_bind _ _ write (fun _ => preserves_pure peer)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native

/-! A saved peer read authorizes a later metadata write only while the exact
resident staged queue and allocation stamp remain at that peer slot. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def SavedPeer (pid : PeerId) (p : Peer) (h : List AuthenticatedEffects.CausalJournal.Event) (w : WGWorld) : Prop :=
  Inv h w ∧ stagedAt w pid = some (p.internalId,p.staged)

theorem read_saved_peer (pid : PeerId) :
    Hoare (getPeer pid) (Inv h) (fun p w => SavedPeer pid p h w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b before run
  obtain ⟨rfl,_,d,device,resident⟩ := getPeer_normal pid w v p a b run
  exact ⟨before,by simp only [stagedAt,device,Option.bind_some,resident,Option.map_some]⟩

theorem saved_peer_store (pid : PeerId) (p : Peer) (action : WG.M α) (same : SameWGStore action) :
    Preserves (SavedPeer pid p h) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  refine ⟨(hoare_iff_run_ambient _ _ _).mp (store same) w a value v b before.1 run,?_⟩
  rw [(ProjectedAction.iff_run_ambient _ _ _).mp (Exact.store same) w a value v b run]
  exact before.2

theorem write_saved_peer (pid : PeerId) (p : Peer) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged) :
    Hoare (setPeer pid (f p)) (SavedPeer pid p h) (fun _ => Inv h) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  have saved : stagedAt w pid = some ((f p).internalId,(f p).staged) := by
    simpa only [(same p).1,(same p).2] using before.2
  have queues := (hoare_iff_run_ambient _ _ _).mp
    (Staged.write_saved (· = stagedAt w) pid (f p)) w a value v b ⟨rfl,saved⟩ run
  have epoch := (ProjectedAction.iff_run_ambient _ _ _).mp
    (PacketOrigins.epoch_ring (TxRing.setPeer_frame pid (f p))) w a value v b run
  apply before.1.retains epoch
  intro target cell found
  simpa only [queues] using found

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
