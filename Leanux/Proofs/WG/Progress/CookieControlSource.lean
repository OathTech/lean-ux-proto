import Leanux.Proofs.WG.Progress.CookieControlModel
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Env.Batch

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

theorem hidden_cookie_control (yielded : Bool) (w : World) (records : List HiddenRecord)
    (present : w.ambient.hidden = some records) :
    (hidden (cookieControlSite yielded) : Leanux.M _).run w =
      match resolveCookieRead yielded records with
      | .error error => .error error
      | .ok (bytes, rest) => .ok (bytes, {w with ambient := {w.ambient with hidden := some rest}}) := by
  change ((AmbientM.hidden (cookieControlSite yielded)).run w.ambient >>= fun (bytes, after) =>
    .ok (bytes, {w with ambient := after})) = _
  cases yielded <;> cases stripped : records.dropWhile (fun r => HiddenSite.passive r.site) with
  | nil =>
    simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart,
      present, HiddenSite.info, cookieControlSite, Worker.sectionId, Worker.index,
      resolveCookieRead, stripped]
    rfl
  | cons record rest =>
    simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart,
      present, HiddenSite.info, cookieControlSite, Worker.sectionId, Worker.index,
      resolveCookieRead, stripped]
    split <;> (try rfl)
    split <;> rfl

theorem cookiePeek_run (w : World) (records : List HiddenRecord)
    (present : w.ambient.hidden = some records) :
    (peekHiddenSite : Leanux.M _).run w = .ok
      (((records.dropWhile (fun r => HiddenSite.passive r.site)).head?).map (·.site),
       {w with ambient := {w.ambient with hidden := some (records.dropWhile (fun r => HiddenSite.passive r.site))}}) := by
  change (AmbientM.peekHiddenSite.run w.ambient >>= fun (result, after) =>
    .ok (result, {w with ambient := after})) = _
  simp [AmbientM.peekHiddenSite, AmbientM.skipAmbient, present]
  cases records.dropWhile (fun r => HiddenSite.passive r.site) <;> rfl

theorem cookieResched_run (w : World) (records : List HiddenRecord)
    (present : w.ambient.hidden = some records) :
    (condResched .receiveWorker).run w =
      match cookieReschedResult records with
      | .error error => .error error
      | .ok (yielded, rest) => .ok (yielded, {w with ambient := {w.ambient with hidden := some rest}}) := by
  simp only [condResched, Worker.resched?]
  rw [StateT.run_bind, cookiePeek_run w records present]
  change ((if cookieNext records != some HiddenSite.reschedReceive.info.id then pure false else
    do let _ ← hidden .reschedReceive; pure true : Leanux.M Bool).run
      {w with ambient := {w.ambient with hidden := some (records.dropWhile (fun r => HiddenSite.passive r.site))}}) = _
  by_cases next : cookieNext records = some HiddenSite.reschedReceive.info.id
  · simp only [next, bne_self_eq_false, Bool.false_eq_true, ite_false]
    have read := hidden_cookie_control true
      {w with ambient := {w.ambient with hidden := some (records.dropWhile (fun r => HiddenSite.passive r.site))}}
      (records.dropWhile (fun r => HiddenSite.passive r.site)) rfl
    simp only [cookieControlSite, ite_true] at read
    rw [StateT.run_bind, read]
    unfold cookieReschedResult
    rw [ite_eq_left next]
    cases resolveCookieRead true (records.dropWhile (fun r => HiddenSite.passive r.site)) with
    | error error => rfl
    | ok pair => rcases pair with ⟨bytes, rest⟩; rfl
  · have different : (cookieNext records != some HiddenSite.reschedReceive.info.id) = true := by
      simp [next]
    rw [different]
    simp only [ite_true, cookieReschedResult, ite_eq_right next]
    rfl

def activationStepSourceWith (iteration : Activation → M IterResult) (_ : Nat) (state : Option Unit × Activation) :
    M (ForInStep (Option Unit × Activation)) := do
  let act := state.2
  match ← iteration act with
  | .ended =>
    let _ ← hidden (.sectionStop act.worker)
    pure (.done (some (), act))
  | .continued => pure (.yield (none, {act with iterations := act.iterations + 1}))
  | .yielded =>
    modifyAmbient fun s => {s with suspended := s.suspended ++ [{act with iterations := act.iterations + 1}]}
    pure (.done (some (), act))


def activationStepSource (_ : Nat) (state : Option Unit × Activation) :
    M (ForInStep (Option Unit × Activation)) :=
  activationStepSourceWith Activation.iter 0 state

def activationFinishSource (a : Activation) (occupancy refills : Nat) (state : Option Unit × Activation) : M Unit :=
  match state.1 with
  | some u => pure u
  | none => invariant s!"{a.worker.symbol} consumed more items than its queue held ({occupancy}) plus the refills its run could take ({refills})"

def activationLoopSourceWith (iteration : Activation → M IterResult) (turns : List Nat)
    (a : Activation) : M (Option Unit × Activation) :=
  forIn turns (none, a) (activationStepSourceWith iteration)

def activationLoopSource (turns : List Nat) (a : Activation) : M (Option Unit × Activation) :=
  activationLoopSourceWith Activation.iter turns a

theorem activation_run_source (a : Activation) :
    Activation.run a = (do
      let occupancy ← Activation.occupancy a
      let refills ← Activation.refills
      let state ← activationLoopSource (List.range' 0 (occupancy + refills + 1)) a
      activationFinishSource a occupancy refills state) := by
  unfold activationLoopSource activationLoopSourceWith activationStepSourceWith activationFinishSource
  simp [Activation.run, Std.Legacy.Range.forIn_eq_forIn_range']
  congr 1
  funext occupancy
  congr 1
  funext refills
  congr 1
  funext state
  rcases state with ⟨result, act⟩
  cases result <;> rfl

end Leanux.Proofs.WG.Progress
