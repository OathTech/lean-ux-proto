import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageFlow
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietActors

/-! A quiet callback preserves both scope and protected-effect coverage only
when its actual source omits both event classes. Native packet or peer writes
are not inferred from this history frame. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged

def observed? (event : Event) : Option Event :=
  match event with
  | .scope _ | .armed _ | .queued _ | .old (.allocated _ _) | .old (.socket _)
      | .keepalivePrepared _ _ | .protocolSocket _ => some event
  | _ => none

private theorem ignored (event : Event) (quiet : observed? event = none) :
    scope? event = none ∧ ¬ Protected event := by
  cases event <;> try exact ⟨rfl,fun h => h.elim⟩
  all_goals try cases quiet
  rename_i value
  cases value <;> first | exact ⟨rfl,fun h => h.elim⟩ | cases quiet

private theorem suffix_ignored (history suffix : List Event)
    (frame : (history ++ suffix).filterMap observed? = history.filterMap observed?) :
    ∀ event ∈ suffix, observed? event = none := by
  have empty : suffix.filterMap observed? = [] := by
    have lengths := congrArg List.length frame
    simp only [List.filterMap_append,List.length_append] at lengths
    apply List.eq_nil_of_length_eq_zero
    omega
  intro event member
  cases found : observed? event with
  | none => rfl
  | some value =>
    have included := List.mem_filterMap.mpr ⟨event,member,found⟩
    rw [empty] at included
    cases included

private theorem quiet_prefix {State : Type} {body : PrefixT Event State α}
    (appends : Appends body) (frame : HistoryFrame observed? body) :
    PrefixEnsures (fun h (_ : State) => Inv frames h) Safe body (fun _ h (_ : State) => Inv frames h) := by
  intro w history ready
  obtain ⟨suffix,grown⟩ := appends w history
  have same := frame w history
  rw [grown] at same
  have absent := suffix_ignored history suffix same
  have kept := ready.quiet suffix
    (fun e member => (ignored e (absent e member)).1)
    (fun e member relevant => ((ignored e (absent e member)).2 relevant).elim)
  refine ⟨suffix,grown,?_,?_⟩
  · rw [grown]; exact kept.1
  · cases result : (runPrefix body w history).1 with
    | error _ => trivial
    | ok value => change Inv frames (runPrefix body w history).2; rw [grown]; exact kept

theorem quiet_product (quiet : CallbackQuiet.ProductQuiet observed? body) : ProductAt frames body :=
  quiet_prefix quiet.1 quiet.2

theorem quiet_state (quiet : CallbackQuiet.StateQuiet observed? body) : StateAt frames body := by
  intro w a history ready
  exact quiet_prefix (frames := frames) (quiet.1 w) (quiet.2 w) a history ready

theorem quiet_selection (pid : PeerId) : StateAt frames (CausalJournal.selection pid) :=
  quiet_state (CallbackQuiet.selection observed? (fun _ => rfl) (fun _ _ => rfl) pid)

theorem quiet_restore (pid : PeerId) (packets : List Packet) : StateAt frames (CausalJournal.stagedRestore pid packets) :=
  quiet_state (CallbackQuiet.restore observed? (fun _ => rfl) pid packets)

theorem quiet_create (pid : PeerId) (item : List SkbId) : StateAt frames (CausalJournal.create pid item) :=
  quiet_state (CallbackQuiet.create observed? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid item)

theorem quiet_encrypt (item : Option (List SkbId)) : ProductAt frames (CausalJournal.encrypt item) :=
  quiet_product (CallbackQuiet.encrypt observed? (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) item)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
