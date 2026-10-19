import Leanux.Proofs.WG.TransmitSecurity.StagedBirth
import Leanux.Proofs.WG.TransmitSecurity.StagedNativeFrames

/-! Native state frames for staged provenance. Surviving peer queues retain
both their ordered packets and allocation stamp; the device epoch is separate. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open AuthenticatedEffects.CausalJournal

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
    have fields := Prod.mk.inj (Option.some.inj (resident.symm.trans changed))
    obtain ⟨rfl,rfl⟩ := fields
    exact births
  · exact (before generation (sameEpoch ▸ atEpoch) q identity values
      ((others q samePeer) ▸ resident)).append_history suffix

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
