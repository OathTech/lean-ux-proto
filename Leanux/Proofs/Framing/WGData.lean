import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.Framing.Lift
import Leanux.WG.Data
import Leanux.Env.IpStack

/-! Padding preserves its native WG world. The concrete checksum helper remains
an actual product action; it reads its packet argument and preserves that world
on normal return. Both retain the original rejected-input Stops. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

theorem calculateSkbPadding_sameWGWorld (len mtu : Nat) :
    SameView (id : WGWorld → WGWorld) (calculateSkbPadding len mtu) := by
  unfold calculateSkbPadding
  apply SameView.bind (fun k => hoare_liftAmbient (AmbientM.branchCmp .padNoMtu _ _ _) (fun w => w = k))
  intro noMtu
  split
  · exact SameView.pure _ _
  · apply SameView.bind (fun k => hoare_liftAmbient (AmbientM.branchCmp .padOverMtu _ _ _) (fun w => w = k))
    intro over
    split
    all_goals
      apply SameView.bind (SameView.pure _ _)
      intro lastUnit
      apply SameView.bind (fun k => hoare_liftAmbient (AmbientM.branch .padClamped _) (fun w => w = k))
      intro clamp
      split
      all_goals
        exact SameView.bind (SameView.pure _ _) (fun _ => SameView.pure _ _)

theorem checksumHelp_sameWorld (pkt : Packet) :
    SameView (id : World → World) (Leanux.Env.checksumHelp pkt) := by
  apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run _ _ _).mpr
  intro w x v hr
  cases hc : pkt.csum with
  | none =>
    simp only [Leanux.Env.checksumHelp, hc] at hr
    cases hr
  | some pair =>
    rcases pair with ⟨start, offset⟩
    let version := (pkt.bytes.headD 0).toNat / 16
    let field := fun off len => ((pkt.bytes.drop off).take len).foldl
      (fun acc b => acc * 256 + b.toNat) 0
    let dst := if version == 4 then field 16 4 else field 24 16
    by_cases hu : Leanux.Env.xmitBytesUnknown (if version == 4 then 4 else 6) dst = true
    · simp only [Leanux.Env.checksumHelp, hc, version, field, dst, hu] at hr
      cases hr
    · by_cases ho : start + offset + 2 > pkt.bytes.length
      · simp only [Leanux.Env.checksumHelp, hc, version, field, dst, hu, ho] at hr
        cases hr
      · simp only [Leanux.Env.checksumHelp, hc, version, field, dst, hu, ho] at hr
        cases hr
        rfl

end Leanux.Proofs.Framing
