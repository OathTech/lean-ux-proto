import Leanux.Proofs.WG.Queues.TxDispositionCuts
import Leanux.Proofs.WG.Queues.TxRxProtection
import Leanux.Proofs.WG.TransmitSecurity.NativeAdapter
import Leanux.Proofs.Logged.NativeCapture

/-! A named source receipt at createData's cleanup entry. The native return
prefix is captured once; cleanup's existing accesses and releases are retained,
including when a later cleanup operation stops. The receipt is a cause marker,
not a completed packet disposal. Only actual WG and Ambient states are recorded. -/
namespace Leanux.Proofs.WG.RetirementSecurity.CreateRefusal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits TransmitSecurity

structure Receipt where
  peer : PeerId
  batch : List SkbId
  first : SkbId
  run : WGRunWitness Int

def Receipt.Valid (r : Receipt) : Prop :=
  r.batch.head?=some r.first ∧ r.run.Valid (createReturnSource r.peer r.batch) ∧
    r.run.value≠0 ∧ r.run.value≠-WG.EPIPE

inductive Event where
  | legacy (value : TxDisposition.Event)
  | refused (value : Receipt)

def legacy? : Event→Option TxDisposition.Event
  | .legacy e=>some e
  | _=>none

def embed (g : TxDisposition.Obs α) : PrefixM Event α :=
  focusPrefix Event.legacy legacy? g

/-- The exact existing createData return prefix, before either success test. -/
def front (pid : PeerId) (item : List SkbId) : TxDisposition.Obs Int := do
  if ← liftPrefix (liftWG (branch .createDataDead (← TxDisposition.nativeAccess (getPeerMixed pid)).isDead)) then
    return -EINVAL
  let ret ← TxDisposition.enqueue pid item
  if ← liftPrefix (liftWG (branch .createDataEpipe (ret == -WG.EPIPE))) then
    TxDisposition.publish item .dead
  return ret

def receipt (pid : PeerId) (item : List SkbId) (first : SkbId) (r : RunWitness Int) : Receipt :=
  ⟨pid,item,first,⟨r.value,r.before.wg,r.after.wg,r.before.ambient,r.after.ambient⟩⟩

def tail (pid : PeerId) (item : List SkbId) (first : SkbId) (r : RunWitness Int) : PrefixM Event Unit := do
  if ← liftPrefix (liftWG (branch .createDataOk (r.value == 0))) then return
  if ← liftPrefix (liftWG (branch .createDataOkEpipe (r.value == -WG.EPIPE))) then return
  emitPrefix (.refused (receipt pid item first r))
  embed (TxDisposition.cleanup pid item first)

def observe (pid : PeerId) (item : List SkbId) : PrefixM Event Unit := do
  let some first := item.head? | liftPrefix (liftWG (invariant "an empty ring item"))
  let r ← captureObserved (embed (front pid item))
  tail pid item first r

def native (pid : PeerId) (item : List SkbId) : WGPrefix Event Unit :=
  NativeAdapter.lower (observe pid item)

private theorem emits (e : E) : Appends (emitPrefix e : PrefixM E Unit) := fun _ _=>⟨[e],rfl⟩

private theorem front_appends (pid : PeerId) (item : List SkbId) : Appends (front pid item) := by
  unfold front TxDisposition.enqueue TxDisposition.enqueueCore TxDisposition.publish
  repeat' first
    | exact Appends.focus _ _ _
    | exact Appends.lift _
    | exact emits _
    | exact Appends.pure _
    | apply Appends.bind
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split

private theorem cleanup_appends (pid : PeerId) (item : List SkbId) (first : SkbId) :
    Appends (TxDisposition.cleanup pid item first) := by
  unfold TxDisposition.cleanup
  repeat' first
    | exact Appends.focus _ _ _
    | exact Appends.pure _
    | apply Appends.bind
    | apply Appends.forIn
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split

private theorem embed_projects (g : TxDisposition.Obs α) (hg : Appends g) :
    ProjectsPrefix legacy? id (embed g) g := hg.project_focus Event.legacy legacy? (fun _=>rfl)

private theorem capture_projects {g : PrefixM Event α} {t : TxDisposition.Obs α}
    (h : ProjectsPrefix legacy? id g t) :
    ProjectsPrefix legacy? StateRunWitness.value (captureObserved g) t := by
  intro w history
  rw [h w history,runPrefix_captureObserved]
  cases runPrefix g w history with
  | mk result events=>cases result <;> rfl

theorem tail_projects (pid : PeerId) (item : List SkbId) (first : SkbId) (r : RunWitness Int) :
    ProjectsPrefix legacy? id (tail pid item first r)
      (TxDisposition.createTail pid item first r.value) := by
  unfold tail TxDisposition.createTail
  apply projectsPrefix_bind legacy? id id (projectsPrefix_lift _ _)
  intro ok
  cases ok with
  | true=>exact projectsPrefix_pure _ _ _
  | false=>
    simp only [Bool.false_eq_true,ite_false,id]
    apply projectsPrefix_bind legacy? id id (projectsPrefix_lift _ _)
    intro pipe
    cases pipe with
    | true=>exact projectsPrefix_pure _ _ _
    | false=>
      simp only [Bool.false_eq_true,ite_false,id]
      have emit : ProjectsPrefix legacy? id
          (emitPrefix (.refused (receipt pid item first r)) : PrefixM Event Unit) (pure ()) :=
        projectsPrefix_emit legacy? _
      simpa only [pure_bind] using projectsPrefix_bind legacy? id id emit
        (fun _=>embed_projects _ (cleanup_appends pid item first))

theorem old_factor (pid : PeerId) (item : List SkbId) : TxDisposition.create pid item = (do
    let some first := item.head? | liftPrefix (liftWG (invariant "an empty ring item"))
    let ret ← front pid item
    TxDisposition.createTail pid item first ret) := by
  simp only [TxDisposition.create_factor,front,bind_assoc,TxDisposition.bind_ite,pure_bind]
  rfl

/-- Exact legacy projection includes every access/release before a later Stop. -/
theorem projects (pid : PeerId) (item : List SkbId) :
    ProjectsPrefix legacy? id (observe pid item) (TxDisposition.create pid item) := by
  rw [old_factor]
  unfold observe
  cases item.head? with
  | none=>exact projectsPrefix_lift _ _
  | some first=>
    apply projectsPrefix_bind legacy? StateRunWitness.value id
      (capture_projects (embed_projects _ (front_appends pid item)))
    intro r
    exact tail_projects pid item first r

theorem erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (observe pid item) (liftWG (createData pid item)) := by
  intro w h
  have old := TxDisposition.create_erases pid item w (h.filterMap legacy?)
  have eq := congrArg Prod.fst (projects pid item w h)
  simp only [id,Prod.eta] at eq
  cases result : (runPrefix (observe pid item) w h).1 <;>
    simpa only [result,Except.map] using eq.symm.trans old

theorem native_erases (pid : PeerId) (item : List SkbId) :
    ErasesStatePrefix (native pid item) (createData pid item) :=
  NativeAdapter.lower_erases (erases pid item)

/-- The native adapter retains the full legacy result, state, Stop and journal. -/
theorem native_projects (pid : PeerId) (item : List SkbId) :
    StateProjectsPrefix legacy? id (native pid item)
      (NativeAdapter.lower (TxDisposition.create pid item)) :=
  NativeAdapter.lower_projects legacy? (projects pid item)

end Leanux.Proofs.WG.RetirementSecurity.CreateRefusal
