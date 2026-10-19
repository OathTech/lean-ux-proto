import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceObserved
import Leanux.Proofs.Logged.PrefixLoops

/-! Ordinary state/history frames for the tagged native source. These do not
authorize packets: the stronger occurrence-dependent callback contract is a
separate obligation. They let existing invariants survive the source refinement. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

variable (I : List E → World → Prop) (S : List E → Prop)
  (safe : ∀ h w, I h w → S h)

include safe

theorem normalList_preserves (callback : List Entry → PrefixM E Unit)
    (hc : ∀ entries, PrefixPreserves I S (callback entries)) (gro : Buffer) :
    PrefixPreserves I S (normalListWith callback gro) := by
  unfold normalListWith
  apply PrefixPreserves.ite
  · intro _; exact PrefixPreserves.pure safe _
  · intro _; exact PrefixPreserves.bind (hc _) (fun _ => PrefixPreserves.pure safe _)

theorem normalOne_preserves (callback : List Entry → PrefixM E Unit)
    (hc : ∀ entries, PrefixPreserves I S (callback entries)) (gro : Buffer) (entry : Entry) (segs : Nat) :
    PrefixPreserves I S (normalOneWith callback gro entry segs) := by
  unfold normalOneWith
  dsimp only
  apply PrefixPreserves.ite
  · intro _; exact normalList_preserves I S safe callback hc _
  · intro _; exact PrefixPreserves.pure safe _

theorem receive_preserves (callback : List Entry → PrefixM E Unit)
    (hc : ∀ entries, PrefixPreserves I S (callback entries)) (gro : Buffer) (entry : Entry) :
    PrefixPreserves I S (receiveWith liftPrefix callback gro entry) := by
  have stopped {α : Type} (message : String) :
      PrefixPreserves I S (liftPrefix (unsupported message : Leanux.M α)) := by
    intro w h hi
    exact ⟨[], by simp, safe h w hi, True.intro⟩
  unfold receiveWith
  repeat' first
    | exact normalOne_preserves I S safe callback hc _ _ _
    | exact PrefixPreserves.pure safe _
    | exact stopped _
    | (with_reducible apply PrefixPreserves.bind)
    | (with_reducible apply PrefixPreserves.ite)
    | (with_reducible intro x; try dsimp only)
    | (split; all_goals try simp_all only [])

theorem flushAll_preserves (callback : List Entry → PrefixM E Unit)
    (hc : ∀ entries, PrefixPreserves I S (callback entries)) (gro : Buffer) :
    PrefixPreserves I S (flushAllWith callback gro) := by
  unfold flushAllWith
  apply PrefixPreserves.bind
  · apply PrefixPreserves.forIn _ _ _ safe
    intro entry g
    exact PrefixPreserves.bind (normalOne_preserves I S safe callback hc g entry 1)
      (fun _ => PrefixPreserves.pure safe _)
  · intro g
    exact PrefixPreserves.bind (normalList_preserves I S safe callback hc {g with held := []})
      (fun _ => PrefixPreserves.pure safe _)

theorem stack_preserves
    (scope : Entry → PrefixM E Unit → PrefixM E Unit)
    (callback : List UInt8 → PrefixM E Unit)
    (hc : ∀ bytes, PrefixPreserves I S (callback bytes))
    (hw : ∀ entry body, PrefixPreserves I S body → PrefixPreserves I S (scope entry body))
    (entries : List Entry) : PrefixPreserves I S (stackWith scope callback entries) :=
  PrefixPreserves.forM entries _ safe (fun entry => hw entry _ (hc entry.bytes))

end Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence

namespace Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePoll
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

elab "gro_frame_head " name:ident : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let type := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let arguments := type.getAppArgs
  unless arguments.size > 0 do Lean.throwError "not a prefix contract"
  let action := arguments.back!.consumeMData
  let .const actual _ := action.getAppFn
    | Lean.throwError "not a constant-headed observer"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different observer head"

theorem source_preserves
    (I : List E → World → Prop) (S : List E → Prop) (safe : ∀ h w, I h w → S h)
    (step : {α : Type} → WG.M α → PrefixM E α)
    (enter : SkbId → RxPacket → PrefixM E Nat) (leave : Nat → PrefixM E Unit)
    (counter : SkbId → RxPacket → PrefixM E Bool)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (receive : GroOccurrence.Buffer → GroOccurrence.Entry → PrefixM E GroOccurrence.Buffer)
    (flush : GroOccurrence.Buffer → PrefixM E Unit)
    (hs : ∀ {α} (action : WG.M α), PrefixPreserves I S (step action))
    (he : ∀ skb pkt, PrefixPreserves I S (enter skb pkt))
    (hl : ∀ token, PrefixPreserves I S (leave token))
    (hc : ∀ skb pkt, PrefixPreserves I S (counter skb pkt))
    (hu : ∀ pid pkt ep, PrefixPreserves I S (consume pid pkt ep))
    (hr : ∀ gro entry, PrefixPreserves I S (receive gro entry))
    (hf : ∀ gro, PrefixPreserves I S (flush gro))
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves I S (sourceWith step enter leave counter consume receive flush pid budget) := by
  unfold sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | exact hs _
    | exact he _ _
    | exact hl _
    | exact hc _ _
    | exact hu _ _ _
    | exact hr _ _
    | exact hf _
    | exact PrefixPreserves.pure safe _
    | (gro_frame_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ safe)
    | (gro_frame_head Bind.bind; apply PrefixPreserves.bind)
    | (gro_frame_head ite; apply PrefixPreserves.ite)
    | (maintenance_intro; try dsimp only)
    | (split; all_goals try simp_all only [])

theorem observed_preserves
    (I : List E → World → Prop) (S : List E → Prop) (safe : ∀ h w, I h w → S h)
    (step : {α : Type} → WG.M α → PrefixM E α)
    (enter : SkbId → RxPacket → PrefixM E Nat) (leave : Nat → PrefixM E Unit)
    (counter : SkbId → RxPacket → PrefixM E Bool)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (scope : GroOccurrence.Entry → PrefixM E Unit → PrefixM E Unit)
    (stack : List UInt8 → PrefixM E Unit)
    (hs : ∀ {α} (action : WG.M α), PrefixPreserves I S (step action))
    (he : ∀ skb pkt, PrefixPreserves I S (enter skb pkt))
    (hl : ∀ token, PrefixPreserves I S (leave token))
    (hc : ∀ skb pkt, PrefixPreserves I S (counter skb pkt))
    (hu : ∀ pid pkt ep, PrefixPreserves I S (consume pid pkt ep))
    (ht : ∀ bytes, PrefixPreserves I S (stack bytes))
    (hw : ∀ entry body, PrefixPreserves I S body → PrefixPreserves I S (scope entry body))
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves I S (observed step enter leave counter consume scope stack pid budget) := by
  have callback := GroOccurrence.stack_preserves I S safe scope stack ht hw
  exact source_preserves I S safe step enter leave counter consume _ _ hs he hl hc hu
    (GroOccurrence.receive_preserves I S safe _ callback)
    (GroOccurrence.flushAll_preserves I S safe _ callback) pid budget

end Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePoll
