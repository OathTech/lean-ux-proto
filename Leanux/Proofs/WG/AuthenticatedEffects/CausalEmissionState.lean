import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionPositions
import Leanux.Proofs.WG.AuthenticatedEffects.ConsumerSentFrames

/-! Native frames and journal bookkeeping for ordered emission accounting.
Only events whose append projection is empty may be treated as quiet. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem state_current (body : Context → WGPrefix Event α) (preserves : ∀ context, StateSafe (body context)) :
    StateSafe (CausalEffects.atCurrent scope? body) := by
  intro w a h hi
  exact preserves (CausalScope.current scope? h) w a h hi

theorem state_receipt (body : WGPrefix Event α) (preserves : StateSafe body)
    (record : WGRunWitness α → Event) (quiet : ∀ run, added (record run) = []) :
    StateSafe (receiptWGObserved body record) :=
  state_bind preserves.captureWGObserved (fun run =>
    state_bind (state_emit (record run) (quiet run)) (fun _ => state_pure run.value))

theorem state_scope (cause : Cause) (body : WGPrefix Event α) (preserves : StateSafe body) :
    StateSafe (CausalScope.scope Event.scope cause body) :=
  CausalScope.scope_preserves Event.scope cause body (fun _ _ _ _ => True.intro)
    (fun _ _ _ _ hi => hi.quiet _ (by
      simp only [emitted,List.flatMap_cons,List.flatMap_nil,added,List.nil_append])) preserves

theorem state_forIn {α β : Type} (xs : List α) (initial : β)
    (body : α → β → WGPrefix Event (ForInStep β))
    (preserves : ∀ value state, StateSafe (body value state)) : StateSafe (forIn xs initial body) := by
  apply StatePrefixEnsures.forInInvariant xs initial (I := fun _ h w _ => Inv h w)
  · intro _ _ _ _ _; trivial
  · exact preserves

open Lean Meta Elab Tactic in
elab "emission_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe || target.isAppOf ``ProductSafe do
    throwError "not an emission carrier contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let .const actual _ := action.getAppFn | throwError "not a constant-headed source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different source head"

macro "emission_step" : tactic => `(tactic| first
  | (emission_head Pure.pure; exact state_pure _)
  | (emission_head Bind.bind; apply state_bind)
  | (emission_head ite; apply state_ite)
  | (emission_head ForIn.forIn; apply state_forIn)
  | maintenance_intro
  | (split; all_goals try simp_all only []; all_goals try subst_vars)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

macro "emission_native" : tactic => `(tactic|
  (emission_head liftWGPrefix
   apply state_native
   sent_frame [] using [getPeer_sent_spec,setPeer_sent_spec,getKeypair_sent_spec,setKeypair_sent_spec]))

theorem protocol_buffer (pid : PeerId) (bytes : List UInt8) :
    StateSafe (ProtocolSocket.observed Event.protocolSocket scope? pid bytes) := by
  unfold ProtocolSocket.observed ProtocolSocket.bufferWith
  repeat' first
    | (emission_head CausalEffects.atCurrent; apply state_current; intro context; exact protocol_socket context _)
    | emission_native
    | emission_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
