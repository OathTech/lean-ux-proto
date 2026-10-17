import Leanux.Proofs.WG.Config.RandomPort

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem hiddenUdp_range (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) :
    Noise.Product.Ensures (liftAmbient (AmbientM.hidden .udpPortDraw))
      (fun w => P w.wg w.fs w.tasks w.seccomp)
      (fun bs w => P w.wg w.fs w.tasks w.seccomp ∧
        LOCAL_PORT_LOW ≤ randomPortFirst (bs.foldr (fun b acc => acc * 256 + b.toNat) 0) ∧
        randomPortFirst (bs.foldr (fun b acc => acc * 256 + b.toNat) 0) ≤ LOCAL_PORT_HIGH) := by
  intro w bs final pre run
  change ((AmbientM.hidden .udpPortDraw).run w.ambient >>= fun (value, after) =>
    .ok (value, {w with ambient := after})) = .ok (bs, final) at run
  cases draw : (AmbientM.hidden .udpPortDraw).run w.ambient with
  | error stop => rw [draw] at run; cases run
  | ok pair =>
    obtain ⟨bytes, after⟩ := pair
    rw [draw] at run
    cases run
    have native : ((hidden .udpPortDraw : StateT Unit AmbientM (List UInt8)).run ()).run w.ambient =
        .ok ((bs, ()), after) := by
      change ((AmbientM.hidden .udpPortDraw).run w.ambient).map
        (fun (value, next) => ((value, ()), next)) = _
      rw [draw]
      rfl
    obtain ⟨_, width⟩ := (ensures_iff _ _ _).mpr (hiddenUdp_shape (fun _ : Unit => True))
      () w.ambient bs () after trivial native
    have bound := littleEndian_bound bs
    rw [width] at bound
    exact ⟨pre, randomPortFirst_range _ bound⟩

end Leanux.Proofs.WG.Config
