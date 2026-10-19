import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalEncryptionSource

/-! Exact callback projection through every original encryption iteration.
Publication repayment receipts disappear only under the stated selector. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.EncryptionSource
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity AuthenticatedEffects Lifetimes
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

structure Ops.Projects (ρ : E → Option F) (g : Ops E) (t : Ops F) : Prop where
  step : ∀ {α} (action : Leanux.M α), ProjectsPrefix ρ id (g.step action) (t.step action)
  head : ∀ skb, ProjectsPrefix ρ id (g.head skb) (t.head skb)
  packet : ∀ headId head skb, ProjectsPrefix ρ id (g.packet headId head skb) (t.packet headId head skb)
  publish : ∀ item state, ProjectsPrefix ρ id (g.publish item state) (t.publish item state)

private theorem loop_projects (ρ : E → Option F) (xs : List α) (initial : β)
    (g : α → β → PrefixM E (ForInStep β)) (t : α → β → PrefixM F (ForInStep β))
    (h : ∀ x b, ProjectsPrefix ρ id (g x b) (t x b)) :
    ProjectsPrefix ρ id (forIn xs initial g) (forIn xs initial t) := by
  induction xs generalizing initial with
  | nil => exact projectsPrefix_pure ρ id initial
  | cons x xs ih =>
    simp only [List.forIn_cons]
    apply projectsPrefix_bind ρ id id (h x initial)
    intro step
    cases step with
    | done b => exact projectsPrefix_pure ρ id b
    | yield b => exact ih b

macro "disposal_encryption_project " h:ident rho:ident : tactic => `(tactic| first
  | exact Ops.Projects.step $h _
  | exact Ops.Projects.head $h _
  | exact Ops.Projects.packet $h _ _ _
  | exact Ops.Projects.publish $h _ _
  | (maintenance_head Pure.pure; exact projectsPrefix_pure $rho id _)
  | (maintenance_head Bind.bind; apply projectsPrefix_bind $rho id id)
  | (maintenance_head ite; apply projectsPrefix_ite $rho _ id)
  | (maintenance_head ForIn.forIn; apply loop_projects $rho)
  | (maintenance_intro; try dsimp only [id])
  | maintenance_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem afterHead_projects (ρ : E → Option F) {g : Ops E} {t : Ops F} (h : Ops.Projects ρ g t)
    (first : List SkbId) (headId : SkbId) (head : RunWitness DataPacket) :
    ProjectsPrefix ρ id (afterHead g first headId head) (afterHead t first headId head) := by
  unfold afterHead
  repeat' disposal_encryption_project h ρ

theorem tail_projects (ρ : E → Option F) {g : Ops E} {t : Ops F} (h : Ops.Projects ρ g t)
    (item : Option (List SkbId)) : ProjectsPrefix ρ id (tail g item) (tail t item) := by
  unfold tail
  repeat' first
    | with_reducible exact afterHead_projects ρ h _ _ _
    | disposal_encryption_project h ρ

theorem focused_projects (ρ : E → Option F)
    (eg : WorkerEncryption.Receipt → E) (dg : E → Option WorkerEncryption.Receipt)
    (et : WorkerEncryption.Receipt → F) (dt : F → Option WorkerEncryption.Receipt)
    (enc : ∀ r, ρ (eg r) = some (et r)) (dec : ∀ e, dg e = (ρ e).bind dt) :
    Ops.Projects ρ (focused eg dg) (focused et dt) := by
  constructor
  all_goals intros
  all_goals exact CompletionEffects.focus_matching ρ eg dg et dt enc dec _

private theorem focus_lift (encode : L → E) (decode : E → Option L) (action : Leanux.M α) :
    focusPrefix encode decode (liftPrefix action) = liftPrefix action := by
  funext w h
  change (action.run w,h ++ ((h.filterMap decode).drop (h.filterMap decode).length).map encode) = _
  simp only [List.drop_length,List.map_nil,List.append_nil]
  rfl

theorem observed_projects (ρ : E → Option F)
    (eg : WorkerEncryption.Receipt → E) (dg : E → Option WorkerEncryption.Receipt)
    (et : WorkerEncryption.Receipt → F) (dt : F → Option WorkerEncryption.Receipt)
    (enc : ∀ r, ρ (eg r) = some (et r)) (dec : ∀ e, dg e = (ρ e).bind dt)
    (disposal : Event → E) (disposalDecode : E → Option Event)
    (quiet : ∀ e, ρ (disposal e) = none) :
    Ops.Projects ρ (observed eg dg disposal disposalDecode) (focused et dt) := by
  refine {focused_projects ρ eg dg et dt enc dec with publish := ?_}
  intro item state
  have projected := (Publication.observed_projects disposal disposalDecode ρ quiet item state).liftWGObserver ρ id
  simpa only [observed,focused,native,focus_lift,liftWGObserver_lift] using projected

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.EncryptionSource
