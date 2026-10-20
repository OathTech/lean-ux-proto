import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionInteriorReadOnly

/-! A fixed source tree for encryption's read-only preparation primitives.
The tree is data, and its points use actual successful left prefixes. No
arbitrary factorization equation constructs an interior source point. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionPrimitive
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity EncryptionInterior

inductive Shape : {α : Type} → Leanux.M α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | primitive (action : Primitive α) : Shape action.native
  | bind {body : Leanux.M α} {next : α → Leanux.M β}
      (head : Shape body) (tail : ∀value,Shape (next value)) : Shape (body >>= next)

noncomputable def preparationShape (packet : DataPacket) : Shape (Encryption.prepare Env.checksumHelp packet) := by
  rw [←prepare_native]
  unfold prepareWith
  repeat' first
    | exact Shape.primitive _
    | exact Shape.pure _
    | apply Shape.bind
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split

inductive Point : {α : Type} → {action : Leanux.M α} → Shape action → World → World → Prop where
  | entry (shape : Shape action) : Point shape w w
  | returned (shape : Shape action) (performed : action.run w=.ok (value,v)) : Point shape w v
  | left {body : Leanux.M α} {next : α → Leanux.M β} {head : Shape body}
      (tail : ∀value,Shape (next value)) (point : Point head w v) : Point (.bind head tail) w v
  | right {body : Leanux.M α} {next : α → Leanux.M β} (head : Shape body)
      (tail : ∀value,Shape (next value)) (leading : body.run w=.ok (value,u))
      (point : Point (tail value) u v) : Point (.bind head tail) w v

variable {α : Type} {action : Leanux.M α} {shape : Shape action}

theorem Point.residual (point : Point shape w v) : ∃remaining : Leanux.M α,action.run w=remaining.run v := by
  induction point with
  | entry shape=>exact ⟨_,rfl⟩
  | returned shape performed=>exact ⟨pure _,performed⟩
  | @left α β w v body next head tail point ih=>
    obtain ⟨rest,same⟩:=ih
    refine ⟨rest >>= next,?_⟩
    simp only [StateT.run_bind,same]
  | right head tail leading point ih=>
    obtain ⟨rest,same⟩:=ih
    refine ⟨rest,?_⟩
    rw [StateT.run_bind,leading]
    exact same

noncomputable def remainder (point : Point shape w v) : Leanux.M α := Classical.choose point.residual

theorem remainder_run (point : Point shape w v) : action.run w=(remainder point).run v :=
  Classical.choose_spec point.residual

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionPrimitive
