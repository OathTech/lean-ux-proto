import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionMaterialFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionFrontObserved

/-! Physical checkpoint evidence is emitted by the very same native callback
run. The evidence remains in its actual prefix if a later continuation stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front.Material
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal

def Stamp (initial : WGWorld) : Event → Prop
  | .stagedDisposal (.overflow _ r) => view r.after = view initial
  | .stagedDisposal (.release _ r) => view r.after = view initial
  | _ => True

def Checked (priorHistory : List Event) (initial : WGWorld) (history : List Event) : Prop :=
  ∃ suffix, history = priorHistory ++ suffix ∧ ∀ event ∈ suffix, Stamp initial event

def State (priorHistory : List Event) (initial : WGWorld)
    (history : List Event) (w : WGWorld) (_a : Ambient) : Prop :=
  Checked priorHistory initial history ∧ view w = view initial

variable {initial : WGWorld} {base : List Event}

theorem Checked.empty (history : List Event) (w : WGWorld) : Checked history w history :=
  ⟨[],by simp,by simp⟩

theorem Checked.append (before : Checked base initial history) (event : Event) (stamp : Stamp initial event) :
    Checked base initial (history ++ [event]) := by
  obtain ⟨suffix,rfl,stamps⟩ := before
  refine ⟨suffix ++ [event],by simp only [List.append_assoc],?_⟩
  intro e member
  rcases List.mem_append.mp member with old | new
  · exact stamps e old
  · have same := List.mem_singleton.mp new
    exact same ▸ stamp

theorem Checked.last (before : Checked base initial (base ++ [event])) : Stamp initial event := by
  obtain ⟨suffix,equal,stamps⟩ := before
  have same : [event] = suffix := List.append_cancel_left equal
  exact stamps event (same ▸ List.mem_singleton_self event)

theorem Checked.checkpoint (before : Checked entry.history entry.world history)
    (cut : Checkpoint entry history ledger snapshot) : view snapshot = view entry.world := by
  cases cut with
  | initial => rfl
  | nonfinal => exact before.last
  | released => exact before.last
  | trimmed => exact before.last

theorem native {action : WG.M α} (frame : SameView view action) :
    StatePrefixPreserves (State base initial) (Checked base initial) (liftWGPrefix action) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ before => before.1)
  intro h w a value v b before run
  exact ⟨before.1,((ProjectedAction.iff_run_ambient _ _ _).mp frame w a value v b run).trans before.2⟩

theorem pure_checked (value : α) :
    StatePrefixEnsures (State base initial) (Checked base initial) (pure value) (fun _ => State base initial) :=
  StatePrefixEnsures.pure _ (fun _ _ _ before => before.1) (fun _ _ _ before => before)

theorem trim_checked (pid : PeerId) :
    StatePrefixPreserves (State base initial) (Checked base initial) (ops.trim pid) := by
  intro w a h before
  have equation := Front.trim_run pid w a h
  change runPrefix ((ops.trim pid).run w) a h = _ at equation
  rw [equation]
  cases run : ((xmitTrim pid).run w).run a with
  | error stop => exact ⟨[],by simp,before.1,True.intro⟩
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    have same := ((ProjectedAction.iff_run_ambient _ _ _).mp (trim pid) w a value v b run).trans before.2
    have history := before.1.append (.stagedDisposal (.overflow pid ⟨value,w,v,a,b⟩)) same
    exact ⟨_,rfl,history,history,same⟩

theorem put_checked (peer : Option PeerId) :
    StatePrefixPreserves (State base initial) (Checked base initial) (ops.put peer) := by
  intro w a h before
  have equation := Front.put_run peer w a h
  change runPrefix ((ops.put peer).run w) a h = _ at equation
  rw [equation]
  cases run : ((HandshakeSecurity.StagedDisposal.releaseCut peer).run w).run a with
  | error stop => exact ⟨[],by simp,before.1,True.intro⟩
  | ok out =>
    rcases out with ⟨⟨value,v⟩,b⟩
    have same := ((ProjectedAction.iff_run_ambient _ _ _).mp (release peer) w a value v b run).trans before.2
    have history := before.1.append (.stagedDisposal (.release peer ⟨value,w,v,a,b⟩)) same
    cases value with
    | none => exact ⟨_,rfl,history,history,same⟩
    | some pair =>
      rcases pair with ⟨pid,p⟩
      refine ⟨_,rfl,history,?_⟩
      dsimp only
      cases done : ((HandshakeSecurity.StagedDisposal.releaseFinish pid p).run v).run b with
      | error stop => trivial
      | ok out =>
        rcases out with ⟨⟨value,u⟩,c⟩
        exact ⟨history,((ProjectedAction.iff_run_ambient _ _ _).mp (finish pid p) v b value u c done).trans same⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission.Front.Material
