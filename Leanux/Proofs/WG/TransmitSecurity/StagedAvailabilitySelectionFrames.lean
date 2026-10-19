import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityHistory

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000
set_option pp.structureInstances false

def Saved (history : List Event) (pid : PeerId) (peer : Peer) (w : WGWorld) : Prop :=
  ∃ generation, Packets.epoch w = some generation ∧
    stagedAt w pid = some (peer.internalId,[]) ∧
    Batch history generation pid peer.internalId peer.staged

theorem Saved.append (saved : Saved h pid peer w) (quiet : Quiet pid suffix) : Saved (h ++ suffix) pid peer w := by
  obtain ⟨generation,epoch,empty,batch⟩ := saved
  exact ⟨generation,epoch,empty,batch.append quiet⟩

theorem Inv.clear (before : Inv h w) (pid : PeerId) (p : Peer) :
    Inv h {w with dev := w.dev.map fun d => {d with peers := d.peers.insert pid {p with staged := []}}} := by
  cases device : w.dev with
  | none =>
    intro generation epoch
    simp [Packets.epoch] at epoch
  | some d =>
    simp only [Option.map_some]
    have slot : stagedAt {w with dev := some {d with peers := d.peers.insert pid {p with staged := []}}} pid =
        some (p.internalId,[]) := by simp [stagedAt]
    simpa only [List.append_nil] using before.changed (generation := d.ifindex) [] (fun _ _ member => by cases member)
      (by simp [Packets.epoch,device]) (by simp [Packets.epoch]) slot
      (fun q different => by simp [stagedAt,device,Std.TreeMap.getElem?_insert,Ne.symm different]) Batch.nil


end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
