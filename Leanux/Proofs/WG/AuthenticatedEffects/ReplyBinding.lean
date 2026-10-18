import Leanux.Proofs.WG.AuthenticatedEffects.ReplySource
import Leanux.Proofs.WG.AuthenticatedEffects.TunnelSource

/-! The reply's destination is the observed input source, including its port.
These local source facts do not claim that routing or allocation succeeds. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.WG.CounterWindow

theorem endpoint_source (src : SkbSource) (w v : WGWorld) (a b : Ambient)
    (result : Option Endpoint)
    (run : ((endpointFromSkb src).run w).run a = .ok ((result,v),b)) :
    ∃ e, result = some e ∧ e.addr = src.saddr ∧ e.port = src.sport ∧
      (e.family = AF_INET ∨ e.family = AF_INET6) := by
  by_cases v4 : src.family = 4
  · simp [endpointFromSkb, v4, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact ⟨_,rfl,rfl,rfl,Or.inl rfl⟩
  · by_cases v6 : src.family = 6
    · by_cases multicast : src.saddr / 2 ^ 120 = 0xff
      · simp [endpointFromSkb, v6, multicast, branch, AmbientM.branch,
          unsupported, AmbientM.unsupported] at run
        cases run
      · simp [endpointFromSkb, v6, multicast, branch, AmbientM.branch] at run
        rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
        exact ⟨_,rfl,rfl,rfl,Or.inr rfl⟩
    · simp [endpointFromSkb, v4, v6, branch, AmbientM.branch,
        invariant, AmbientM.invariant] at run
      cases run

theorem replyFront_source (src : SkbSource) (w v : WGWorld) (a b : Ambient)
    (target : ReplyTarget)
    (run : ((replyFront src).run w).run a = .ok ((some target,v),b)) :
    target.endpoint.addr = src.saddr ∧ target.endpoint.port = src.sport := by
  simp only [replyFront, StateT.run_bind, branch, StateT.run_monadLift,
    monadLift_self, branch_run, except_ok_bind, StateT.run_pure, except_pure, Bool.false_eq_true, ↓reduceIte] at run
  cases epRun : ((endpointFromSkb src).run w).run (record a .replyInSkbNull false) with
  | error err => simp [epRun] at run
  | ok out =>
    rcases out with ⟨⟨ep,u⟩,c⟩
    obtain ⟨endpoint,eq,addr,port,family⟩ := endpoint_source src w u _ c ep epRun
    subst ep
    rw [epRun] at run
    simp only [except_ok_bind, Option.isNone_some, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, branch_run, StateT.run_pure, except_pure, Bool.false_eq_true, ↓reduceIte] at run
    cases alloc : ((hiddenAlloc .replySkb : WG.M Bool).run u).run
      (record c .replyEndpointErr false) with
    | error err => simp [alloc] at run
    | ok out =>
      rcases out with ⟨⟨allocated,z⟩,d⟩
      rw [alloc] at run
      cases allocated <;> simp [branch_run] at run
      all_goals split at run <;> simp_all
      all_goals rcases run with ⟨⟨eq,_⟩,_⟩; subst target; exact ⟨addr,port⟩

end Leanux.Proofs.WG.AuthenticatedEffects
