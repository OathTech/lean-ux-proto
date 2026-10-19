import Leanux.Proofs.WG.TimerDiscipline.SendPeerFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

-- Local native Std.Do variant of campaign 1's Framing.hoare_liftRouting.
private theorem hoare_liftRouting_variant {α : Type} (action : Net.M α)
    (P : WGWorld → Prop) (stable : ∀ g routing, P g → P {g with routing}) :
    Ensures (liftRouting action) P (fun _ => P) := by
  intro g ambient result final after pre run
  change (((action.run {toRouting := g.routing, wg0 := g.dev.map fun d =>
    {running := d.running, inet4Dev := d.inet4Dev}}).run ambient) >>=
    fun ((value, routing), inputs) =>
      .ok ((value, {g with routing := routing.toRouting}), inputs)) = _ at run
  cases routed : (action.run {toRouting := g.routing, wg0 := g.dev.map fun d =>
    {running := d.running, inet4Dev := d.inet4Dev}}).run ambient with
  | error stop => rw [routed] at run; cases run
  | ok pair =>
    obtain ⟨⟨value, routing⟩, inputs⟩ := pair
    rw [routed] at run
    cases run
    exact stable g routing.toRouting pre

theorem send4_sendWorkView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (q : Option SendWorkDevice) (v : Option SendWorkPeer) :
    ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ send4 e (some pid) bytes ds exactRx
      ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
  let P : WGWorld → Prop := fun g => sendWorkAt g pid = (q, v)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g ambient y final after pre run; cases run; exact pre
  have hgetdev : Ensures getDev P (fun _ => P) := by
    intro g ambient d final after pre run
    cases device : g.dev with
    | none =>
      simp [getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
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
    hoare_liftRouting_variant action P (fun _ _ pre => pre)
  have hgetrouting : Ensures (getRouting : WG.M Net.Routing) P (fun _ => P) := by
    intro g ambient result final after pre run
    change Except.ok ((g.routing, g), ambient) = _ at run
    cases run
    exact pre
  have hstop {α : Type} (message : String) :
      Ensures (invariant message : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run
    simp [invariant, AmbientM.invariant] at run
    cases run
  have hclear : Ensures (do
      let p ← getPeer pid
      setPeer pid {p with endpoint := p.endpoint.map fun x => {x with src := 0, srcIf := 0}}) P (fun _ => P) := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_sendWorkView pid q v)) ?_
    intro p
    have same : sendWorkPeer
        {p with endpoint := p.endpoint.map fun x => {x with src := 0, srcIf := 0}} = sendWorkPeer p := by
      simp only [sendWorkPeer, sendWorkCell, initiationView, Option.map_map,
        Function.comp_def, Roaming.destination, socketEndpoint]
      rfl
    simpa only [same] using
      (ensures_iff _ _ _).mpr (setPeer_sendWorkView pid q v
        {p with endpoint := p.endpoint.map fun x => {x with src := 0, srcIf := 0}})
  have clearBind {α : Type} (next : WG.M α)
      (rest : Ensures next P (fun _ => P)) :
      Ensures (do
        let p ← getPeer pid
        setPeer pid {p with endpoint := p.endpoint.map fun x => {x with src := 0, srcIf := 0}}
        next) P (fun _ => P) := by
    simpa only [bind_assoc] using
      (ensures_bind _ (fun _ => next) hclear (fun _ => rest))
  have hcache (gen : Nat) : Ensures (dstCacheGet pid gen) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (dstCacheGet_sendWorkView pid gen q v)
  have hreset : Ensures (dstCacheReset pid) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (dstCacheReset_sendWorkView pid q v)
  have hset (src gen dev : Nat) : Ensures (dstCacheSet pid src gen dev) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (dstCacheSet_sendWorkView pid src gen dev q v)
  have htx (r : Route) : Ensures (tunnelXmit e bytes ds r exactRx) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (tunnelXmit_sendWorkView pid e bytes ds r exactRx q v)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (yesFrame : Ensures yes P (fun _ => P)) (noFrame : Ensures no P (fun _ => P)) :
      Ensures (if condition then yes else no) P (fun _ => P) := by
    split <;> assumption
  apply (ensures_iff _ _ _).mp
  change Ensures _ P (fun _ => P)
  unfold send4
  simp only [Option.get!_some]
  repeat' first
    | exact hpure _
    | exact hgetdev
    | exact hbranch _ _
    | exact hnet _
    | exact hgetrouting
    | exact hstop _
    | exact hclear
    | exact hcache _
    | exact hreset
    | exact hset _ _ _
    | exact htx _
    | (apply clearBind)
    | (apply branchBind)
    | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (refine hif _ _ _ ?_ ?_)

  all_goals rename_i cached
  all_goals cases cached
  all_goals
    repeat' first
      | exact hpure _
      | exact hgetdev
      | exact hbranch _ _
      | exact hnet _
      | exact hgetrouting
      | exact hstop _
      | exact hclear
      | exact hcache _
      | exact hreset
      | exact hset _ _ _
      | exact htx _
      | (apply clearBind)
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
      | exact hgetrouting
      | exact hstop _
      | exact hclear
      | exact hcache _
      | exact hreset
      | exact hset _ _ _
      | exact htx _
      | (apply clearBind)
      | (apply branchBind)
      | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
      | (refine hif _ _ _ ?_ ?_)

theorem send6_sendWorkView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (q : Option SendWorkDevice) (v : Option SendWorkPeer) :
    ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ send6 e (some pid) bytes ds exactRx
      ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄ := by
  let P : WGWorld → Prop := fun g => sendWorkAt g pid = (q, v)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g ambient y final after pre run; cases run; exact pre
  have hgetdev : Ensures getDev P (fun _ => P) := by
    intro g ambient d final after pre run
    cases device : g.dev with
    | none =>
      simp [getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
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
    hoare_liftRouting_variant action P (fun _ _ pre => pre)
  have hgetrouting : Ensures (getRouting : WG.M Net.Routing) P (fun _ => P) := by
    intro g ambient result final after pre run
    change Except.ok ((g.routing, g), ambient) = _ at run
    cases run
    exact pre
  have hstop {α : Type} (message : String) :
      Ensures (invariant message : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run
    simp [invariant, AmbientM.invariant] at run
    cases run
  have hclear : Ensures (do
      let p ← getPeer pid
      setPeer pid {p with endpoint := p.endpoint.map fun x => {x with src := 0}}) P (fun _ => P) := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_sendWorkView pid q v)) ?_
    intro p
    have same : sendWorkPeer
        {p with endpoint := p.endpoint.map fun x => {x with src := 0}} = sendWorkPeer p := by
      simp only [sendWorkPeer, sendWorkCell, initiationView, Option.map_map,
        Function.comp_def, Roaming.destination, socketEndpoint]
      rfl
    simpa only [same] using
      (ensures_iff _ _ _).mpr (setPeer_sendWorkView pid q v
        {p with endpoint := p.endpoint.map fun x => {x with src := 0}})
  have clearBind {α : Type} (next : WG.M α)
      (rest : Ensures next P (fun _ => P)) :
      Ensures (do
        let p ← getPeer pid
        setPeer pid {p with endpoint := p.endpoint.map fun x => {x with src := 0}}
        next) P (fun _ => P) := by
    simpa only [bind_assoc] using
      (ensures_bind _ (fun _ => next) hclear (fun _ => rest))
  have hcache (gen : Nat) : Ensures (dstCacheGet pid gen) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (dstCacheGet_sendWorkView pid gen q v)
  have hreset : Ensures (dstCacheReset pid) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (dstCacheReset_sendWorkView pid q v)
  have hset (src gen dev : Nat) : Ensures (dstCacheSet pid src gen dev) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (dstCacheSet_sendWorkView pid src gen dev q v)
  have htx (r : Route) : Ensures (tunnelXmit e bytes ds r exactRx) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (tunnelXmit_sendWorkView pid e bytes ds r exactRx q v)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (yesFrame : Ensures yes P (fun _ => P)) (noFrame : Ensures no P (fun _ => P)) :
      Ensures (if condition then yes else no) P (fun _ => P) := by
    split <;> assumption
  apply (ensures_iff _ _ _).mp
  change Ensures _ P (fun _ => P)
  unfold send6
  simp only [Option.get!_some]
  repeat' first
    | exact hpure _
    | exact hgetdev
    | exact hbranch _ _
    | exact hnet _
    | exact hgetrouting
    | exact hstop _
    | exact hclear
    | exact hcache _
    | exact hreset
    | exact hset _ _ _
    | exact htx _
    | (apply clearBind)
    | (apply branchBind)
    | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
    | (refine hif _ _ _ ?_ ?_)

  all_goals rename_i cached
  all_goals cases cached
  all_goals
    repeat' first
      | exact hpure _
      | exact hgetdev
      | exact hbranch _ _
      | exact hnet _
      | exact hgetrouting
      | exact hstop _
      | exact hclear
      | exact hcache _
      | exact hreset
      | exact hset _ _ _
      | exact htx _
      | (apply clearBind)
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
      | exact hgetrouting
      | exact hstop _
      | exact hclear
      | exact hcache _
      | exact hreset
      | exact hset _ _ _
      | exact htx _
      | (apply clearBind)
      | (apply branchBind)
      | (refine ensures_bind (Q := fun _ => P) _ _ ?_ (fun _ => ?_))
      | (refine hif _ _ _ ?_ ?_)

theorem send4_sendView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ send4 e (some pid) bytes ds exactRx
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  exact send_frame_of_sendWork_native (send4 e (some pid) bytes ds exactRx) pid
    (send4_sendWorkView pid e bytes ds exactRx) q v

theorem send6_sendView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (q : Option TableCursor) (v : Option InitiationView) :
    ⦃fun w => ⌜sendAt w pid = (q, v)⌝⦄ send6 e (some pid) bytes ds exactRx
      ⦃⇓? _ w => ⌜sendAt w pid = (q, v)⌝⦄ := by
  exact send_frame_of_sendWork_native (send6 e (some pid) bytes ds exactRx) pid
    (send6_sendWorkView pid e bytes ds exactRx) q v

theorem send4_initiationView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ send4 e (some pid) bytes ds exactRx
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  exact initiation_frame_of_send_native (send4 e (some pid) bytes ds exactRx) pid (send4_sendView pid e bytes ds exactRx) v

theorem send6_initiationView (pid : PeerId) (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ send6 e (some pid) bytes ds exactRx
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  exact initiation_frame_of_send_native (send6 e (some pid) bytes ds exactRx) pid (send6_sendView pid e bytes ds exactRx) v

end Leanux.Proofs.WG.TimerDiscipline
