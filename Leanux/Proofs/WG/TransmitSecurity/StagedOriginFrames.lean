import Leanux.Proofs.WG.TransmitSecurity.StagedOrigins
import Leanux.Proofs.WG.TransmitSecurity.StagedNativeFrames

/-! Native state frames for staged provenance. Surviving peer queues retain
both their ordered packets and allocation stamp; the device epoch is separate. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

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

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
