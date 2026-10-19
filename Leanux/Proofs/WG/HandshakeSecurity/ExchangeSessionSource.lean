import Leanux.Proofs.WG.HandshakeSecurity.AllocationClaims
import Leanux.Proofs.WG.Origins.SessionMaterial

/-! Source consequences of a completed native session. The allocation front
and the clear/rotation/index suffix are consecutive in this one execution;
normal false returns never enter the suffix. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Exchange
open Leanux Leanux.WG Leanux.Proofs.Logged MaterialOrigin

theorem session_tail_true (pid slot : Nat) (w v : WGWorld) (a b : Ambient) (result : Bool)
    (run : ((SessionOrigin.tail pid slot).run w).run a = .ok ((result,v),b)) : result = true := by
  unfold SessionOrigin.tail SessionOrigin.tailWith at run
  simp only [bind_ok_ambient] at run
  obtain ⟨_,u,c,_,peer,z,d,_,alive,t,e,_,rest⟩ := run
  cases alive with
  | false => cases rest
  | true =>
    simp only [↓reduceIte,bind_ok_ambient] at rest
    obtain ⟨_,u,c,_,_,z,d,_,replaced,t,e,_,rest⟩ := rest
    cases replaced with
    | false => cases rest
    | true =>
      simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte] at rest
      cases rest
      rfl

theorem session_false_world (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((beginSession pid).run w).run a = .ok ((false,v),b)) : v = w := by
  rw [SessionOrigin.factor,bind_ok_ambient] at run
  obtain ⟨result,u,c,front,tail⟩ := run
  cases result with
  | none =>
    cases tail
    exact Origins.front_none pid w v a b front
  | some context =>
    exact False.elim (Bool.noConfusion (session_tail_true pid context.slot u v c b false tail))

theorem session_true_front (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((beginSession pid).run w).run a = .ok ((true,v),b)) :
    ∃ context middle clock,
      ((SessionOrigin.front pid).run w).run a = .ok ((some context,middle),clock) ∧
      ((SessionOrigin.tail pid context.slot).run middle).run clock = .ok ((true,v),b) := by
  rw [SessionOrigin.factor,bind_ok_ambient] at run
  obtain ⟨result,middle,clock,front,tail⟩ := run
  cases result with
  | none => cases tail
  | some context => exact ⟨context,middle,clock,front,tail⟩

end Leanux.Proofs.WG.HandshakeSecurity.Exchange
