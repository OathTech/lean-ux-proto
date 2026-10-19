import Leanux.Proofs.WG.TransmitSecurity.StagedAvailability
import Leanux.Proofs.WG.TransmitSecurity.StagedAllocationOrigins

/-! Native state frames for the unconsumed-birth carrier. The allocation
transition needs the actual saved peer's empty queue, not just an origin. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open AuthenticatedEffects.CausalJournal Leanux.Proofs.WG.TransmitSecurity.Staged.Origins

theorem Inv.retains (before : Inv history w) (sameEpoch : Packets.epoch v = Packets.epoch w)
    (retained : Staged.Retains w v) : Inv history v := by
  intro generation epoch pid stamp packets resident
  exact before generation (sameEpoch ▸ epoch) pid stamp packets (retained pid (stamp,packets) resident)

theorem frame {action : WG.M α} (epoch : SameView Packets.epoch action)
    (queues : Staged.Frame action) : Preserves (Inv history) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  exact before.retains
    ((ProjectedAction.iff_run_ambient _ _ _).mp epoch w a value v b run)
    ((hoare_iff_run_ambient _ _ _).mp (queues w) w a value v b (.refl w) run)

theorem Inv.changed (before : Inv history w) (suffix : List Event)
    (quiet : ∀ pid, Quiet pid suffix)
    (sameEpoch : Packets.epoch v = Packets.epoch w)
    (atEpoch : Packets.epoch v = some generation)
    (changed : stagedAt v pid = some (stamp,packets))
    (others : ∀ q, q ≠ pid → stagedAt v q = stagedAt w q)
    (births : Batch (history ++ suffix) generation pid stamp packets) :
    Inv (history ++ suffix) v := by
  intro epoch foundEpoch q identity values resident
  have sameGeneration : epoch = generation := Option.some.inj (foundEpoch.symm.trans atEpoch)
  subst epoch
  by_cases samePeer : q = pid
  · subst q
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (resident.symm.trans changed))
    exact births
  · exact (before generation (sameEpoch ▸ atEpoch) q identity values
      ((others q samePeer) ▸ resident)).append (quiet q)

theorem allocation_other (packets : List DataPacket) (r : WGRunWitness (List SkbId))
    (owner : ∀ packet ∈ packets, packet.peer = pid) (different : q ≠ pid) :
    Quiet q [.old (.allocated packets r)] := by
  intro event member used
  have same : event = .old (.allocated packets r) := List.mem_singleton.mp member
  subst event
  obtain ⟨packet,inside,peer⟩ := used
  exact different (peer.symm.trans (owner packet inside))

/-- Allocation consumes all live birth credits of the peer whose queue was
selected. Other peers keep their credits even when payloads are identical. -/
theorem allocated_inv (packets : List DataPacket) (r : WGRunWitness (List SkbId))
    (valid : r.Valid (packets.mapM newTxSkb)) (before : Inv history r.before)
    (empty : ∀ stamp staged, stagedAt r.before pid = some (stamp,staged) → staged = [])
    (owner : ∀ packet ∈ packets, packet.peer = pid) :
    Inv (history ++ [.old (.allocated packets r)]) r.after := by
  have epoch := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Origins.allocate_epoch packets) _ _ _ _ _ valid
  have queues := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Origins.allocate_staged packets) _ _ _ _ _ valid
  intro generation atEpoch q stamp staged resident
  have old : stagedAt r.before q = some (stamp,staged) := by simpa only [queues] using resident
  by_cases same : q = pid
  · subst q
    rw [empty stamp staged old]
    exact .nil
  · exact (before generation (epoch ▸ atEpoch) q stamp staged old).append
      (allocation_other packets r owner same)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
