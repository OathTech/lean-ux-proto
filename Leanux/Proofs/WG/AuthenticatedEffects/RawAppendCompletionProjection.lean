import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendLifetime
import Leanux.Proofs.WG.Lifetimes.ProductAmbient

/-! The causal TX observer projects to the independent original-append source.
Local lifetime/disposal events are quiet; each socket receipt corresponds to
the actual final native append, with preceding other-family appends retained. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

theorem focused_completion_projects (rho : E → Option Event)
    (encode : Completion.Event → E) (decode : E → Option Completion.Event)
    (matching : ∀ event, rho (encode event) = completion? event) :
    CompletionEffects.Ops.Projects rho (CompletionEffects.focused encode decode) completionOps where
  step := fun action => focused_projects encode decode completion? rho matching _ _
    (Appends.lift _) (Independent.lift _) (completion_ops_projects.step action)
  peer := fun pid => focused_projects encode decode completion? rho matching _ _
    (Appends.focus _ _ _) (Independent.lift _) (completion_ops_projects.peer pid)
  modifyPeer := fun pid f => focused_projects encode decode completion? rho matching _ _
    (Appends.focus _ _ _) (Independent.lift _) (completion_ops_projects.modifyPeer pid f)
  packet := fun skb => focused_projects encode decode completion? rho matching _ _
    (Appends.focus _ _ _) (Independent.lift _) (completion_ops_projects.packet skb)
  completion := fun pid item => focused_projects encode decode completion? rho matching _ _
    (fun _ _ => ⟨[.disposition (.completion pid item)],rfl⟩) (Independent.pure _)
    (completion_ops_projects.completion pid item)
  send := fun pid skb packet => focused_projects encode decode completion? rho matching _ _
    ((pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsNative.«0».Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffects.send_appends) pid skb packet)
    (transport_independent pid packet) (completion_ops_projects.send pid skb packet)
  drop := fun pid item => focused_projects encode decode completion? rho matching _ _
    (Appends.focus _ _ _) (Independent.lift _) (completion_ops_projects.drop pid item)
  dispose := fun pid item key => focused_projects encode decode completion? rho matching _ _
    (Appends.focus _ _ _) (Independent.lift _) (completion_ops_projects.dispose pid item key)
  traversal := fun pid => focused_projects encode decode completion? rho matching _ _
    (Appends.focus _ _ _) (Independent.lift _) (completion_ops_projects.traversal pid)
  sent := fun pid => focused_projects encode decode completion? rho matching _ _
    (Appends.focus _ _ _) (Independent.lift _) (completion_ops_projects.sent pid)
  dataSent := fun pid => focused_projects encode decode completion? rho matching _ _
    (Appends.focus _ _ _) (Independent.lift _) (completion_ops_projects.dataSent pid)
  fresh := fun pid => focused_projects encode decode completion? rho matching _ _
    (Appends.focus _ _ _) (Independent.lift _) (completion_ops_projects.fresh pid)

theorem observed_completion_projects (rho : E → Option Event)
    (encode : Completion.Event → E) (decode : E → Option Completion.Event)
    (matching : ∀ event, rho (encode event) = completion? event)
    (scope : E → Option (CausalScope.Event Cause))
    (arm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (queue : TimerEffects.Queued (CausalEffects.Context Cause) → E)
    (armQuiet : ∀ r, rho (arm r) = none) (queueQuiet : ∀ r, rho (queue r) = none) :
    CompletionEffects.Ops.Projects rho
      (CompletionEffects.observed encode decode scope arm queue) completionOps := by
  have effects := LifetimeEffects.decorate_projects rho _ _
    (lifetime_base_projects rho encode decode (fun event => matching (CompletionEffects.lifetimeEvent event)))
    scope arm queue armQuiet queueQuiet
  refine {focused_completion_projects rho encode decode matching with traversal := ?_, dataSent := ?_, fresh := ?_}
  · intro pid
    have projected := (LifetimeEffects.traversal_projects rho effects pid).liftWGObserver rho id
    simpa only [CompletionEffects.observed,completionOps,lifetime_traversal,liftWGObserver_lift] using projected
  · intro pid
    have projected := (LifetimeEffects.dataSent_projects rho effects pid).liftWGObserver rho id
    simpa only [CompletionEffects.observed,completionOps,lifetime_dataSent,liftWGObserver_lift] using projected
  · intro pid
    have projected := (LifetimeEffects.fresh_projects rho effects pid).liftWGObserver rho id
    simpa only [CompletionEffects.observed,completionOps,lifetime_fresh,liftWGObserver_lift] using projected

theorem observed_completion_step (rho : E → Option Event)
    (encode : Completion.Event → E) (decode : E → Option Completion.Event)
    (matching : ∀ event, rho (encode event) = completion? event)
    (recordScope : CausalScope.Event Cause → E) (scope : E → Option (CausalScope.Event Cause))
    (cause : PeerId → List SkbId → Cause)
    (arm : TimerEffects.Arm (CausalEffects.Context Cause) → E)
    (queue : TimerEffects.Queued (CausalEffects.Context Cause) → E)
    (scopeQuiet : ∀ r, rho (recordScope r) = none)
    (armQuiet : ∀ r, rho (arm r) = none) (queueQuiet : ∀ r, rho (queue r) = none) (pid : PeerId) :
    ProjectsPrefix rho id
      (CompletionEffects.observedStep encode decode recordScope scope cause arm queue pid)
      (completion pid) :=
  CompletionEffects.stepScoped_projects rho recordScope cause scopeQuiet
    (observed_completion_projects rho encode decode matching scope arm queue armQuiet queueQuiet) pid

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
