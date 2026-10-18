import Leanux.Proofs.WG.Roaming.RemoteControlModel
import Leanux.Proofs.WG.Roaming.RemoteCompletionSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteControl
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits Leanux.Proofs.Framing Std.Do

theorem setPeerEndpoint_invalid (pid : PeerId) (endpoint : Endpoint)
    (invalid4 : endpoint.family ≠ AF_INET) (invalid6 : endpoint.family ≠ AF_INET6) :
    SameView (fun g : WGWorld => g) (setPeerEndpoint pid endpoint) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  unfold setPeerEndpoint at run
  simp only [requireNotPending,pure_bind] at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,middle,a,read,rest⟩ := run
  obtain ⟨sameWorld,sameAmbient,_⟩ := getPeer_normal pid g middle p ambient a read
  subst middle
  subst a
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨same,compared,b,compare,rest⟩ := rest
  obtain ⟨value,out,tail,execution,valueEq,stateEq⟩ :=
    Config.endpointEq_returns_exact endpoint p.endpoint (fun w => w = g) g ambient rfl
  rw [compare] at execution
  cases execution
  subst compared
  cases same <;>
    simp [branch,AmbientM.branch,invalid4,invalid6] at rest
  all_goals obtain ⟨⟨rfl,rfl⟩,rfl⟩ := rest; rfl

end Leanux.Proofs.WG.Roaming.RemoteControl
