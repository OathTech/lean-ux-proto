import Leanux.Proofs.WG.Index.StagedFrames
import Leanux.Proofs.WG.TimerDiscipline.SendPeerFrames
import Leanux.Proofs.WG.Index.ReceiveOperations
import Leanux.Proofs.WG.Roaming.EndpointSource
import Leanux.Proofs.WG.Roaming.ResponseCallProductSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem receiveStats_tables (len : Nat) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄
      modifyDev (fun d => {d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + len})
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  cases run
  exact tablesSafe_of_cursor g _ (by simp only [Option.map_map]; rfl) pre

theorem endpointFromSkb_tables (src : SkbSource) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ endpointFromSkb src
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  exact ((ensures_iff _ _ _).mpr (Roaming.endpointFromSkb_exact src TablesSafeWG)
    g ambient result final after pre run).1

theorem dstCacheReset_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ dstCacheReset pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  have h := (ensures_iff _ _ _).mpr
    (TimerDiscipline.dstCacheReset_sendView pid
      (TimerDiscipline.sendAt g pid).1 (TimerDiscipline.sendAt g pid).2)
    g ambient result final after rfl run
  exact tablesSafe_of_cursor g final (congrArg Prod.fst h) pre

theorem timersHandshakeComplete_tables (pid : PeerId) (site : HiddenSite) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ timersHandshakeComplete pid site
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have read : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient result final after pre run).1
  apply (ensures_iff _ _ _).mp
  unfold timersHandshakeComplete delTimer
  simp only [bind_assoc]
  refine ensures_bind _ _ read ?_
  intro p
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (setPeer_tables pid _)) ?_
  intro _
  refine ensures_bind _ _ read ?_
  intro p
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (setPeer_tables pid _)) ?_
  intro _
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
    (hoare_liftAmbient_variant (AmbientM.hidden site) TablesSafeWG)) ?_
  intro now
  refine ensures_bind _ _ read ?_
  intro p
  exact (ensures_iff _ _ _).mpr (setPeer_tables pid _)

theorem timersAnyAuthenticatedPacketReceived_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ timersAnyAuthenticatedPacketReceived pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold timersAnyAuthenticatedPacketReceived delTimer
  have read : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient result final after pre run).1
  exact ensures_bind _ _ read (fun p => (ensures_iff _ _ _).mpr (setPeer_tables pid _))

theorem tunnelXmit_tables (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ TimerDiscipline.tunnelXmit e bytes ds r exactRx
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  have h := (ensures_iff _ _ _).mpr
    (TimerDiscipline.tunnelXmit_sendView 0 e bytes ds r exactRx
      (TimerDiscipline.sendAt g 0).1 (TimerDiscipline.sendAt g 0).2)
    g ambient result final after rfl run
  exact tablesSafe_of_cursor g final (congrArg Prod.fst h) pre

theorem makeCookie_tables (src : SkbSource) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ makeCookie src
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hdev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) :
      Ensures (branchCmp site value lhs rhs : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branchCmp site value lhs rhs) TablesSafeWG)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if condition then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by
    split <;> assumption
  have hmodify (birthdate : Int64) (secret : List UInt8) :
      Ensures (modifyDev fun d => {d with cookieSecretBirthdate := birthdate, cookieSecret := secret})
        TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact tablesSafe_of_cursor g _ (by simp only [Option.map_map]; rfl) pre
  apply (ensures_iff _ _ _).mp
  unfold makeCookie branchExpired birthdateTest
  simp only [bind_assoc, pure_bind]
  repeat' first
    | exact hpure _
    | exact hdev
    | exact hambient _
    | exact hbranch _ _
    | exact hcmp _ _ _ _
    | exact hmodify _ _
    | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | (refine hif _ _ _ ?_ ?_)

theorem cookieMessageCreate_tables (index : Nat) (src : SkbSource) (mac1 : List UInt8) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ cookieMessageCreate index src mac1
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hdev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  apply (ensures_iff _ _ _).mp
  unfold cookieMessageCreate
  refine ensures_bind _ _ (hambient (AmbientM.hidden .cookieNonce)) ?_
  intro nonce
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (makeCookie_tables src)) ?_
  intro cookie
  refine ensures_bind _ _ hdev ?_
  intro d
  exact hpure _

theorem setPeerEndpointFromSkb_tables (pid : PeerId) (src : SkbSource) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ setPeerEndpointFromSkb pid src
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  have hread : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient result final after pre run).1
  have hset (p : Peer) : Ensures (setPeer pid p) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (setPeer_tables pid p)
  have hreset : Ensures (dstCacheReset pid) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (dstCacheReset_tables pid)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if condition then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by
    split <;> assumption
  have heq (a : Endpoint) (b : Option Endpoint) :
      Ensures (endpointEq a b) TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold endpointEq WG.andM
    repeat' first
      | exact hpure _
      | exact hbranch _ _
      | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
      | (refine hif _ _ _ ?_ ?_)
  apply (ensures_iff _ _ _).mp
  unfold setPeerEndpointFromSkb
  refine ensures_bind (Q := fun _ => TablesSafeWG) _ _
    ((ensures_iff _ _ _).mpr (endpointFromSkb_tables src)) ?_
  intro endpoint
  cases endpoint with
  | none =>
    have stop : Ensures (invariant "unreachable" : WG.M Unit) TablesSafeWG (fun _ => TablesSafeWG) := by
      intro g ambient result final after pre run
      simp [invariant, AmbientM.invariant] at run
      cases run
    repeat' first
      | exact hpure _
      | exact hbranch _ _
      | exact stop
      | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
      | (refine hif _ _ _ ?_ ?_)
  | some e =>
    unfold setPeerEndpoint requireNotPending
    simp only [pure_bind]
    repeat' first
      | exact hpure _
      | exact hbranch _ _
      | exact hread
      | exact hset _
      | exact hreset
      | exact heq _ _
      | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
      | (refine hif _ _ _ ?_ ?_)

theorem ratelimiterAllow_tables (src : SkbSource) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ ratelimiterAllow src
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) :
      Ensures (branchCmp site value lhs rhs : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branchCmp site value lhs rhs) TablesSafeWG)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if condition then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by
    split <;> assumption
  have hget : Ensures (get : WG.M WGWorld) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hmodify (f : WGWorld → WGWorld) (same : ∀ g, (f g).dev = g.dev) :
      Ensures (modify f : WG.M Unit) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact tablesSafe_of_cursor g _ (congrArg (Option.map TimerDiscipline.tableCursor) (same g)) pre
  have hstop {α : Type} (message : String) : Ensures (invariant message : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; simp [invariant, AmbientM.invariant] at run; cases run
  have hunsupported {α : Type} (message : String) : Ensures (unsupported message : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; simp [unsupported, AmbientM.unsupported] at run; cases run
  apply (ensures_iff _ _ _).mp
  unfold ratelimiterAllow
  repeat' first
    | exact hpure _
    | exact hget
    | exact hambient _
    | exact hbranch _ _
    | exact hcmp _ _ _ _
    | exact hstop _
    | exact hunsupported _
    | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | (refine hif _ _ _ ?_ ?_)
  all_goals rename_i family
  all_goals rcases family with ⟨v6, ip⟩
  all_goals cases v6
  all_goals dsimp only
  all_goals
    repeat' first
      | exact hpure _
      | exact hget
      | exact hambient _
      | exact hbranch _ _
      | exact hcmp _ _ _ _
      | exact hstop _
      | exact hunsupported _
      | exact hmodify _ (fun _ => rfl)
      | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
      | (refine hif _ _ _ ?_ ?_)
      | split

theorem cookieValidatePacket_tables (msg : List UInt8) (src : SkbSource) (checkCookie : Bool) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ cookieValidatePacket msg src checkCookie
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hdev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if condition then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by
    split <;> assumption
  have hc := (ensures_iff _ _ _).mpr (makeCookie_tables src)
  have hr := (ensures_iff _ _ _).mpr (ratelimiterAllow_tables src)
  apply (ensures_iff _ _ _).mp
  unfold cookieValidatePacket
  repeat' first
    | exact hpure _
    | exact hdev
    | exact hbranch _ _
    | exact hc
    | exact hr
    | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | (refine hif _ _ _ ?_ ?_)

-- Local variant of campaign 1's native routing lift frame.
private theorem hoare_liftRouting_tables_variant {α : Type} (action : Net.M α) :
    Ensures (liftRouting action) TablesSafeWG (fun _ => TablesSafeWG) := by
  intro g ambient result final after pre run
  change (((action.run {toRouting := g.routing, wg0 := g.dev.map fun d =>
    {running := d.running, inet4Dev := d.inet4Dev}}).run ambient) >>= fun ((value, routing), inputs) =>
      .ok ((value, {g with routing := routing.toRouting}), inputs)) = _ at run
  cases routed : (action.run {toRouting := g.routing, wg0 := g.dev.map fun d =>
    {running := d.running, inet4Dev := d.inet4Dev}}).run ambient with
  | error stop => rw [routed] at run; cases run
  | ok pair =>
    obtain ⟨⟨value, routing⟩, inputs⟩ := pair
    rw [routed] at run
    cases run
    exact pre

theorem send4_reply_tables (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ send4 e none bytes ds exactRx
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hdev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if condition then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by
    split <;> assumption
  have branchBind {α : Type} (site : Decision) (value : Bool) (next : Bool → WG.M α)
      (rest : Ensures (next value) TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (branch site value >>= next) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    change ((next value).run g).run {ambient with steps := ambient.steps.push {
      decision := site, outcome := value, netRx := ambient.netRxSection}} = _ at run
    exact rest g _ result final after pre run
  have hrouting : Ensures (getRouting : WG.M Net.Routing) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hstop {α : Type} (message : String) : Ensures (invariant message : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; simp [invariant, AmbientM.invariant] at run; cases run
  have htx (r : Route) := (ensures_iff _ _ _).mpr (tunnelXmit_tables e bytes ds r exactRx)
  apply (ensures_iff _ _ _).mp
  unfold send4
  repeat' first
    | exact hpure _
    | exact hdev
    | exact hbranch _ _
    | exact hoare_liftRouting_tables_variant _
    | exact hrouting
    | exact hstop _
    | exact htx _
    | apply branchBind
    | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | (refine hif _ _ _ ?_ ?_)
    | split

  all_goals rename_i routed
  all_goals cases routed
  all_goals
    repeat' first
      | exact hpure _
      | exact hdev
      | exact hbranch _ _
      | exact hoare_liftRouting_tables_variant _
      | exact hrouting
      | exact hstop _
      | exact htx _
      | apply branchBind
      | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
      | (refine hif _ _ _ ?_ ?_)
      | split

theorem send6_reply_tables (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ send6 e none bytes ds exactRx
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hdev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if condition then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by
    split <;> assumption
  have branchBind {α : Type} (site : Decision) (value : Bool) (next : Bool → WG.M α)
      (rest : Ensures (next value) TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (branch site value >>= next) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    change ((next value).run g).run {ambient with steps := ambient.steps.push {
      decision := site, outcome := value, netRx := ambient.netRxSection}} = _ at run
    exact rest g _ result final after pre run
  have hrouting : Ensures (getRouting : WG.M Net.Routing) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hstop {α : Type} (message : String) : Ensures (invariant message : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; simp [invariant, AmbientM.invariant] at run; cases run
  have htx (r : Route) := (ensures_iff _ _ _).mpr (tunnelXmit_tables e bytes ds r exactRx)
  apply (ensures_iff _ _ _).mp
  unfold send6
  repeat' first
    | exact hpure _
    | exact hdev
    | exact hbranch _ _
    | exact hoare_liftRouting_tables_variant _
    | exact hrouting
    | exact hstop _
    | exact htx _
    | apply branchBind
    | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | (refine hif _ _ _ ?_ ?_)
    | split

theorem sendBufferAsReplyToSkb_tables (src : SkbSource) (buffer : List UInt8) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ sendBufferAsReplyToSkb src buffer
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if condition then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by
    split <;> assumption
  have he := (ensures_iff _ _ _).mpr (endpointFromSkb_tables src)
  have h4 (e : Endpoint) := (ensures_iff _ _ _).mpr (send4_reply_tables e buffer 0 false)
  have h6 (e : Endpoint) := (ensures_iff _ _ _).mpr (send6_reply_tables e buffer 0 false)
  have hstop {α : Type} (message : String) : Ensures (invariant message : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; simp [invariant, AmbientM.invariant] at run; cases run
  apply (ensures_iff _ _ _).mp
  unfold sendBufferAsReplyToSkb
  repeat' first
    | exact hpure _
    | exact hbranch _ _
    | exact hambient _
    | exact hstop _
    | exact he
    | exact h4 _
    | exact h6 _
    | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | (refine hif _ _ _ ?_ ?_)
    | split

theorem sendHandshakeCookie_tables (msg : List UInt8) (src : SkbSource) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ sendHandshakeCookie msg src
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold sendHandshakeCookie
  exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (cookieMessageCreate_tables _ src _))
    (fun buffer => (ensures_iff _ _ _).mpr (sendBufferAsReplyToSkb_tables src buffer))

private theorem responseLoad_tables :
    Ensures Roaming.responseLoad TablesSafeWG (fun _ => TablesSafeWG) := by
  have hpure {α : Type} (value : α) : Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hdev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have hambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) :
      Ensures (branchCmp site value lhs rhs : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branchCmp site value lhs rhs) TablesSafeWG)
  have hif {α : Type} (condition : Prop) [Decidable condition] (yes no : WG.M α)
      (hy : Ensures yes TablesSafeWG (fun _ => TablesSafeWG))
      (hn : Ensures no TablesSafeWG (fun _ => TablesSafeWG)) :
      Ensures (if condition then yes else no) TablesSafeWG (fun _ => TablesSafeWG) := by
    split <;> assumption
  have hget : Ensures (get : WG.M WGWorld) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hmodify (last : Option Int64) :
      Ensures (modify fun g : WGWorld => {g with lastUnderLoad := last}) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; cases run; exact pre
  have hstop {α : Type} (message : String) : Ensures (invariant message : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run; simp [invariant, AmbientM.invariant] at run; cases run
  unfold Roaming.responseLoad birthdateTest
  simp only [bind_assoc, pure_bind]
  repeat' first
    | exact hpure _
    | exact hdev
    | exact hget
    | exact hbranch _ _
    | exact hcmp _ _ _ _
    | exact hambient _
    | exact hmodify _
    | exact hstop _
    | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | (refine hif _ _ _ ?_ ?_)
    | split

theorem receiveLoadThen_tables_native (next : Bool → WG.M Unit)
    (body : ∀ b, ⦃fun g => ⌜TablesSafeWG g⌝⦄ next b ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ receiveLoadThen next ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  rw [← Roaming.responseLoad_source]
  exact (ensures_iff _ _ _).mp (ensures_bind _ _ responseLoad_tables
    (fun b => (ensures_iff _ _ _).mpr (body b)))

namespace Product

theorem receiveLoadThen_tables (next : Bool → Leanux.M Unit)
    (body : ∀ b, ⦃fun w => ⌜TablesSafeWG w.wg⌝⦄ next b ⦃⇓? _ w => ⌜TablesSafeWG w.wg⌝⦄) :
    ⦃fun w => ⌜TablesSafeWG w.wg⌝⦄ Roaming.Product.receiveLoadThen next
      ⦃⇓? _ w => ⌜TablesSafeWG w.wg⌝⦄ := by
  rw [← Roaming.Product.responseLoad_source]
  apply (Noise.Product.ensures_iff _ _ _).mp
  refine Noise.Product.ensures_bind (Q := fun _ w => TablesSafeWG w.wg) _ _ ?_
    (fun b => (Noise.Product.ensures_iff _ _ _).mpr (body b))
  intro w result final pre run
  change (((Roaming.responseLoad.run w.wg).run w.ambient) >>= fun ((value, current), inputs) =>
    .ok (value, {w with wg := current, ambient := inputs})) = _ at run
  cases executed : (Roaming.responseLoad.run w.wg).run w.ambient with
  | error stop => rw [executed] at run; cases run
  | ok pair =>
    obtain ⟨⟨value, current⟩, inputs⟩ := pair
    rw [executed] at run
    cases run
    exact responseLoad_tables w.wg w.ambient _ current inputs pre executed

end Product

end Leanux.Proofs.WG.Index
