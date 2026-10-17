import Leanux.Proofs.WG.Index.NewlinkFrames
import Leanux.Proofs.WG.TimerDiscipline.SendView
import Leanux.Proofs.WG.Noise.AccessSource

/-! Existing within-WireGuard table frames. Cursor equality retains both
numeric/owner table uniqueness and the hashed-keypair allocation bound. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem tablesSafe_of_cursor (g final : WGWorld)
    (same : final.dev.map TimerDiscipline.tableCursor = g.dev.map TimerDiscipline.tableCursor)
    (safe : TablesSafeWG g) : TablesSafeWG final := by
  cases before : g.dev <;> cases after : final.dev <;>
    simp_all [TablesSafeWG, TimerDiscipline.tableCursor, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

theorem setPeer_tables (pid : PeerId) (p : Peer) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ setPeer pid p
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
    {d with peers := d.peers.insert pid p})}), ambient) = _ at run
  cases run
  intro final present
  cases device : g.dev with
  | none => simp [device] at present
  | some d =>
    simp only [device, Option.map_some, Option.some.injEq] at present
    subst final
    exact pre d device

theorem addMacToPacket_tables (pid : PeerId) (msg : List UInt8) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ addMacToPacket pid msg
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  have hpure {α : Type} (value : α) :
      Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hread : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient result final after pre run).1
  have hclock (birth : Int64) :
      Ensures (branchExpired .addMacCookieFresh birth COOKIE_FRESH_SECONDS (!·))
        TablesSafeWG (fun _ => TablesSafeWG) := by
    simp only [branchExpired, birthdateTest, bind_assoc, pure_bind]
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _
      (hambient (AmbientM.hiddenClock64 .birthdateExpired)) ?_
    intro now
    exact hambient (AmbientM.branchCmp _ _ _ _)
  unfold addMacToPacket
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ hread ?_
  intro p
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _
    ((ensures_iff _ _ _).mpr (setPeer_tables pid _)) ?_
  intro _
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ ?_
  · unfold WG.andM
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _
      (hambient (AmbientM.branch .addMacCookieValid p.cookieIsValid)) ?_
    intro valid
    cases valid with
    | false => exact hpure false
    | true => exact hclock p.cookieBirthdate
  · intro fresh
    cases fresh <;> exact hpure _

end Leanux.Proofs.WG.Index
