import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionCompletionSocket
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionEffects
import Leanux.Proofs.Logged.FocusedInvariant
import Leanux.Proofs.WG.AuthenticatedEffects.CausalFocusSource

/-! Exact transport-send composition. Each real socket append is covered
before the subsequent peer accounting, and all lifetime accesses retain their
own journal positions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity Queues
set_option maxHeartbeats 600000

theorem completion_access (body : MixedM α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (frame : SameView WGWorld.sent native) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.access body)) :=
  product_observed _ native (focusPrefix_erases _ _ (Completion.access_erases erases))
    (Appends.focus _ _ _) (completion_access_quiet body) frame

private abbrev Focused (body : PrefixM Completion.Event α) :=
  FocusedInvariant (fun h w => Inv h w.wg) (fun _ => True)
    (Event.old ∘ Journal.completionEvent) completion? body

private theorem inverse (e : Completion.Event) :
    completion? ((Event.old ∘ Journal.completionEvent) e) = some e := by cases e <;> rfl

private theorem access (body : MixedM α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (frame : SameView WGWorld.sent native) :
    Focused (Completion.access body) :=
  ⟨Appends.focus _ _ _,completion_access body native erases frame⟩

private theorem peer (pid : PeerId) : Focused (Completion.access (getPeerMixed pid)) :=
  access _ _ (getPeerMixed_erases pid) (by
    sent_frame [] using [getPeer_sent_spec])

private theorem modify_peer (pid : PeerId) (f : Peer → Peer) :
    Focused (Completion.access (modifyPeerKeysPrefix pid f)) :=
  access _ _ (modifyPeerKeysPrefix_erases pid f) (by
    sent_frame [] using [getPeer_sent_spec,setPeer_sent_spec])

private theorem socket (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) : Focused (Completion.socket pid id packet peer ipv4) := by
  refine ⟨?_,completion_socket pid id packet peer ipv4⟩
  unfold Completion.socket
  exact (by cases ipv4 <;> exact Appends.focus _ _ _ : Appends _).receiptObserved

private theorem capture (body : PrefixM Completion.Event α) (safe : Focused body) :
    Focused (captureObserved body) := by
  refine ⟨safe.1.captureObserved,?_⟩
  rw [← (CausalFocus.capture (Event.old ∘ Journal.completionEvent) completion?
    (CausalFocus.native _ _ body safe.1)).2]
  exact safe.2.captureObserved

private theorem native (action : WG.M α) (frame : SameView WGWorld.sent action) :
    Focused (liftPrefix (liftWG action)) :=
  FocusedInvariant.lift _ _ _ (product_wg action (state_native action frame))

open Lean Meta Elab Tactic in
elab "emission_completion_source " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Focused || target.isAppOf ``FocusedInvariant do throwError "not a focused emission contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let action := if action.isAppOf ``Completion.access then action.getAppArgs.back!.consumeMData.headBeta else action
  let .const actual _ := action.getAppFn | throwError "not a constant source callback"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different focused source callback"

theorem completion_send (pid : PeerId) (id : SkbId) (packet : RunWitness DataPacket) : ProductSafe
    (focusPrefix (Event.old ∘ Journal.completionEvent) completion? (Completion.send pid id packet)) := by
  suffices source : Focused (Completion.send pid id packet) from source.2
  unfold Completion.send
  repeat' first
    | (emission_completion_source getPeerMixed; exact peer _)
    | (emission_completion_source modifyPeerKeysPrefix; exact modify_peer _ _)
    | (emission_completion_source Completion.socket; exact socket _ _ _ _ _)
    | (emission_completion_source captureObserved; apply capture)
    | (emission_completion_source liftPrefix; apply native; sent_frame [] using [])
    | (emission_completion_source Pure.pure; exact FocusedInvariant.pure _ _ (fun _ _ _ => True.intro) _)
    | (emission_completion_source Bind.bind; apply FocusedInvariant.bind inverse)
    | (emission_completion_source ite; apply FocusedInvariant.ite)
    | maintenance_intro
    | (split; all_goals try simp_all only []; all_goals try subst_vars)
    | dsimp (config := {failIfUnchanged := true}) only

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
