import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeLifecycleSource
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeRemovalErasure

/-! Result and Stop erasure for all lifecycle callbacks that can drain send work. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.SendExchange
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

variable (sg : {α : Type} → WG.M α → WGPrefix E α)
  (hs : ∀ {α} (a : WG.M α), ErasesStatePrefix (sg a) a)
  (dg : Option PeerId → WGPrefix E Unit)
  (hd : ∀ peer, ErasesStatePrefix (dg peer) (drainHandshakeSendWq peer))

include hs hd in
theorem stop_erases : ErasesStatePrefix (stopWith sg dg) wgStop := by
  unfold stopWith wgStop
  repeat' first
    | exact hs _
    | exact timersStop_erases sg hs dg hd _
    | work_root_erasure_step

include hs hd in
theorem down_erases : ErasesStatePrefix (downWith sg dg) wgDown := by
  unfold downWith wgDown
  exact erasesStatePrefix_bind (hs _) (fun _ => stop_erases sg hs dg hd)

include hs hd in
theorem destruct_erases : ErasesStatePrefix (destructWith sg dg) wgDestruct := by
  rw [Configuration.wgDestruct_factor]
  unfold destructWith Configuration.destructWith
  repeat' first
    | exact hs _
    | exact removeAll_erases sg hs dg hd
    | work_root_erasure_step

theorem envDown_erases {down : PrefixM E Unit} (hd : ErasesPrefix down (liftWG wgDown)) :
    ErasesPrefix (envDownWith (fun {_} a => liftPrefix a) down) Env.wgDown := by
  rw [← envDown_factor]
  unfold envDownWith
  repeat' first
    | exact hd
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (maintenance_intro; try dsimp only)
    | split
  all_goals simp_all only [Option.some.injEq]
  all_goals contradiction

theorem envDelete_erases {down destruct : PrefixM E Unit}
    (hd : ErasesPrefix down (liftWG wgDown)) (hx : ErasesPrefix destruct (liftWG wgDestruct)) :
    ErasesPrefix (envDeleteWith (fun {_} a => liftPrefix a) down destruct) Env.wgDelete := by
  rw [← envDelete_factor]
  unfold envDeleteWith Configuration.envDeleteWith
  repeat' first
    | exact hd
    | exact hx
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

end Leanux.Proofs.WG.HandshakeSecurity.SendExchange
