import Leanux.Proofs.WG.Noise.SocketTagFrames
import Leanux.Proofs.Framing.Lift

/-! Uncached reply sending has no peer-cache writes. The routing adapter and
existing owned tunnel-send contract carry its tag and next-slot cells; no cache layer is copied. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG TimerDiscipline Std.Do

theorem uncached_sendWorkView (pid : PeerId) (six : Bool) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (q : Option SendWorkDevice) (v : Option SendWorkPeer) :
    ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄
      (if six then send6 e none bytes ds exactRx else send4 e none bytes ds exactRx)
      ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
  let P : WGWorld → Prop := fun g => sendWorkAt g pid = (q, v)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g a y v b pre run; cases run; exact pre
  have hgetdev : Ensures getDev P (fun _ => P) := by
    intro g ambient d final after pre run
    cases device : g.dev with
    | none =>
      simp [getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have branchBind {α : Type} (site : Decision) (value : Bool) (next : Bool → WG.M α)
      (rest : Ensures (next value) P (fun _ => P)) :
      Ensures (branch site value >>= next) P (fun _ => P) := by
    intro g ambient result final after pre run
    change ((next value).run g).run {ambient with steps := ambient.steps.push {
      decision := site, outcome := value, netRx := ambient.netRxSection}} = _ at run
    exact rest g _ result final after pre run
  have hnet {α : Type} (action : Net.M α) :
      Ensures (liftRouting action) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr
      (Leanux.Proofs.Framing.hoare_liftRouting action P (fun _ _ pre => pre))
  have hrouting : Ensures (getRouting : WG.M Net.Routing) P (fun _ => P) := by
    intro g a y v b pre run; cases run; exact pre
  have hstop {α : Type} (message : String) :
      Ensures (invariant message : WG.M α) P (fun _ => P) := by
    intro g a y v b pre run
    simp [invariant, AmbientM.invariant] at run
    cases run
  have htx (r : Route) : Ensures (tunnelXmit e bytes ds r exactRx) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (tunnelXmit_sendWorkView pid e bytes ds r exactRx q v)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (hy : Ensures yes P (fun _ => P)) (hn : Ensures no P (fun _ => P)) :
      Ensures (if condition then yes else no) P (fun _ => P) := by split <;> assumption
  apply (ensures_iff _ _ _).mp
  change Ensures _ P (fun _ => P)
  cases six <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals first | unfold send4 | unfold send6
  all_goals
    repeat' first
      | exact hpure _
      | exact hgetdev
      | exact hbranch _ _
      | exact hnet _
      | exact hrouting
      | exact hstop _
      | exact htx _
      | (apply branchBind)
      | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
      | (refine hif _ _ _ ?_ ?_)
  all_goals rename_i routed
  all_goals cases routed
  all_goals
    repeat' first
      | exact hpure _
      | exact hgetdev
      | exact hbranch _ _
      | exact hnet _
      | exact hrouting
      | exact hstop _
      | exact htx _
      | (apply branchBind)
      | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
      | (refine hif _ _ _ ?_ ?_)

private theorem uncached_tagMap (six : Bool) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (entry : Option Device) :
    Ensures (if six then send6 e none bytes ds exactRx else send4 e none bytes ds exactRx)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) :=
  tagMap_frame_of_sendWork _ 0 (uncached_sendWorkView 0 six e bytes ds exactRx) entry

/-- Uncached variant of the shared IPv4 send frame, retaining every tag. -/
theorem send4_spec_tagMap_uncached_variant (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (entry : Option Device) :
    Ensures (send4 e none bytes ds exactRx)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) :=
  uncached_tagMap false e bytes ds exactRx entry

/-- Uncached variant of the shared IPv6 send frame, retaining every tag. -/
theorem send6_spec_tagMap_uncached_variant (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (entry : Option Device) :
    Ensures (send6 e none bytes ds exactRx)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) :=
  uncached_tagMap true e bytes ds exactRx entry

end Leanux.Proofs.WG.Noise
