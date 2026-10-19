import Leanux.Proofs.WG.AuthenticatedEffects.DeliverySource
import Leanux.Proofs.WG.Queues.PollPreservation

/-! Exact projection and source-composition laws for the delivery boundary.
History contracts are explicitly independent of native state invariants. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.DeliverySource
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Lifetimes
open Queues RxJoint.PollSource
set_option maxHeartbeats 600000

theorem afterBatch_projects {E F : Type} (ρ : E → Option F)
    (crypt send sendOne : PrefixM E Unit) (crypt' send' sendOne' : PrefixM F Unit)
    (schedule : Option Worker → PrefixM E Unit) (schedule' : Option Worker → PrefixM F Unit)
    (drained : String → List Bool → PrefixM E Unit) (drained' : String → List Bool → PrefixM F Unit)
    (hc : ProjectsPrefix ρ id crypt crypt') (hs : ProjectsPrefix ρ id send send')
    (ho : ProjectsPrefix ρ id sendOne sendOne')
    (hsch : ∀ stack, ProjectsPrefix ρ id (schedule stack) (schedule' stack))
    (hd : ∀ what flags, ProjectsPrefix ρ id (drained what flags) (drained' what flags))
    (deliver : PrefixM E Unit) (deliver' : PrefixM F Unit)
    (hdeliver : ProjectsPrefix ρ id deliver deliver') :
    ProjectsPrefix ρ id (afterBatchWith crypt send sendOne schedule drained deliver)
      (afterBatchWith crypt' send' sendOne' schedule' drained' deliver') := by
  unfold afterBatchWith
  repeat' first
    | (poll_source_head deliver; exact hdeliver)
    | (poll_source_head crypt; exact hc)
    | (poll_source_head send; exact hs)
    | (poll_source_head sendOne; exact ho)
    | (poll_source_head schedule; exact hsch _)
    | (poll_source_head drained; exact hd _ _)
    | (poll_source_head runWorkerPrefix; apply runWorkerPrefix_projects ρ)
    | (poll_source_head liftPrefix; exact projectsPrefix_lift ρ _)
    | (poll_source_head Pure.pure; first | exact projectsPrefix_pure ρ id _ | exact projectsPrefix_pure ρ (projectStep id) _)
    | (poll_source_head Bind.bind; first | apply projectsPrefix_bind ρ id id | apply projectsPrefix_bind ρ id (projectStep id))
    | (poll_source_head ForIn.forIn; first | apply projectsPrefix_forIn ρ id | apply projectsPrefix_range ρ id)
    | (poll_source_head ite; apply projectsPrefix_ite)
    | maintenance_intro
    | dsimp only [id]
    | split

theorem afterBatch_appends {E : Type} (crypt send sendOne : PrefixM E Unit)
    (schedule : Option Worker → PrefixM E Unit) (drained : String → List Bool → PrefixM E Unit)
    (hc : Appends crypt) (hs : Appends send) (ho : Appends sendOne)
    (hsch : ∀ stack, Appends (schedule stack)) (hd : ∀ what flags, Appends (drained what flags))
    (deliver : PrefixM E Unit) (hdeliver : Appends deliver) :
    Appends (afterBatchWith crypt send sendOne schedule drained deliver) := by
  unfold afterBatchWith
  repeat' first
    | (poll_source_head deliver; exact hdeliver)
    | (poll_source_head crypt; exact hc)
    | (poll_source_head send; exact hs)
    | (poll_source_head sendOne; exact ho)
    | (poll_source_head schedule; exact hsch _)
    | (poll_source_head drained; exact hd _ _)
    | (poll_source_head runWorkerPrefix
       apply (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.runWorker_appends))
    | (poll_source_head liftPrefix; exact Appends.lift _)
    | (poll_source_head Pure.pure; exact Appends.pure _)
    | (poll_source_head Bind.bind; apply Appends.bind)
    | (poll_source_head ForIn.forIn; first | apply Appends.forIn | apply Appends.range)
    | (poll_source_head ite; apply Appends.ite)
    | maintenance_intro
    | dsimp only
    | split

theorem observe_projects (ρ : E → Option F) (deliver : PrefixM E Unit) (deliver' : PrefixM F Unit)
    (h : ProjectsPrefix ρ id deliver deliver') :
    ProjectsPrefix ρ id (observeWith deliver) (observeWith deliver') :=
  projectsPrefix_bind ρ id id (projectsPrefix_lift ρ observeFront) (fun _ =>
    projectsPrefix_bind ρ id id h (fun _ => projectsPrefix_lift ρ observeFinish))

theorem observe_appends (deliver : PrefixM E Unit) (h : Appends deliver) : Appends (observeWith deliver) :=
  (Appends.lift observeFront).bind (fun _ => h.bind (fun _ => Appends.lift observeFinish))

abbrev HistorySafe (Good : List E → Prop) (body : PrefixM E α) :=
  PrefixPreserves (fun h _ => Good h) Good body

private theorem history_lift (Good : List E → Prop) (action : Leanux.M α) :
    HistorySafe Good (liftPrefix action) :=
  PrefixEnsures.lift (P := fun h _ => Good h) (S := Good) (Q := fun _ h _ => Good h)
    action (fun _ _ hi => hi) (fun _ _ _ _ hi _ => hi)

theorem observe_history (Good : List E → Prop) (deliver : PrefixM E Unit) (h : HistorySafe Good deliver) :
    HistorySafe Good (observeWith deliver) :=
  PrefixPreserves.bind (history_lift Good observeFront) (fun _ =>
    PrefixPreserves.bind h (fun _ => history_lift Good observeFinish))

theorem afterBatch_history (Good : List E → Prop)
    (crypt send sendOne : PrefixM E Unit) (schedule : Option Worker → PrefixM E Unit)
    (drained : String → List Bool → PrefixM E Unit) (deliver : PrefixM E Unit)
    (hc : HistorySafe Good crypt) (hs : HistorySafe Good send) (ho : HistorySafe Good sendOne)
    (hsch : ∀ stack, HistorySafe Good (schedule stack))
    (hd : ∀ what flags, HistorySafe Good (drained what flags)) (hdeliver : HistorySafe Good deliver) :
    HistorySafe Good (afterBatchWith crypt send sendOne schedule drained deliver) := by
  change PrefixPreserves (fun h _ => Good h) Good _
  unfold afterBatchWith
  repeat' first
    | (poll_preserve_head crypt; exact hc)
    | (poll_preserve_head send; exact hs)
    | (poll_preserve_head sendOne; exact ho)
    | (poll_preserve_head schedule; exact hsch _)
    | (poll_preserve_head drained; exact hd _ _)
    | (poll_preserve_head deliver; exact hdeliver)
    | (poll_preserve_head liftPrefix; exact history_lift Good _)
    | (poll_preserve_head Pure.pure; apply PrefixPreserves.pure; intro h w hi; exact hi)
    | (poll_preserve_head Bind.bind; apply PrefixPreserves.bind)
    | (poll_preserve_head ForIn.forIn; first | apply PrefixPreserves.forIn | apply PrefixPreserves.range)
    | (poll_preserve_head ite; apply PrefixPreserves.ite)
    | (intro h w hi; exact hi)
    | maintenance_intro
    | dsimp only
    | split

end Leanux.Proofs.WG.AuthenticatedEffects.DeliverySource
