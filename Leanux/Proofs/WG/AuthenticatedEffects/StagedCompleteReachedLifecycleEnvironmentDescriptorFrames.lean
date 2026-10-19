import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecycleEnvironmentDescriptorSource

/-! Descriptor plumbing retains the exact native WG-store and history.
The stronger deletion input is preserved up to its actual guarded callback. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment.Descriptor
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal Points

inductive Atom : {α : Type} → Leanux.M α → Type 1 where
  | fs (body : FS.M α) : Atom (liftFS body)
  | ambient (body : AmbientM α) : Atom (liftAmbient body)
  | read : Atom (get : Leanux.M World)
  | files : Atom (getFiles : Leanux.M FilesStruct)
  | task : Atom (getTask .task)
  | nextFile (fid : Nat) : Atom (modify fun w=>{w with fs:={w.fs with nextFile:=fid}})
  | modifyFiles (f : FilesStruct→FilesStruct) : Atom (Leanux.modifyFiles f)

theorem Atom.store (atom : Atom body) : SameView (fun w : World=>wgStoreView w.wg) body := by
  cases atom with
  | fs body => exact fun initial=>productFS_spec body _ (fun _ _ _ _ before=>before)
  | ambient body => exact fun initial=>productAmbient_spec body _ (fun _ _ before=>before)
  | read => exact fun initial=>(hoare_iff_run _ _ _).mpr (fun w _ _ before run=>by cases run; exact before)
  | files => exact fun initial=>productFS_spec (getFiles : FS.M FilesStruct) _ (fun _ _ _ _ before=>before)
  | task => exact fun initial=>productFS_spec (monadLift (TaskM.getTask .task) : FS.M Task) _ (fun _ _ _ _ before=>before)
  | nextFile => exact fun initial=>(hoare_iff_run _ _ _).mpr (fun w _ _ before run=>by cases run; exact before)
  | modifyFiles f => exact fun initial=>productFS_spec (monadLift (TaskM.modifyTask .task (fun t=>{t with files:=f t.files})) : FS.M Unit) _ (fun _ _ _ _ before=>before)

theorem Atom.frame (atom : Atom body) : SameView (fun w : World=>StagedEntry.view w.wg) body :=
  atom.store.of_factor (fun s : WGStoreView=>StagedEntry.view {dev:=s.dev}) _ (fun _=>rfl)

noncomputable def Atom.shape (atom : Atom body) : Shape (liftPrefix body) := .native (.quiet body atom.frame)

structure Stable (P : List Event→World→Prop) : Prop where
  account : ∀ h w,P h w→Account h w
  store : ∀ h w v,wgStoreView v.wg=wgStoreView w.wg→P h w→P h v

theorem Stable.normal (stable : Stable P) (atom : Atom body) (before : P h w)
    (performed : runPrefix (liftPrefix body) w h=(.ok (value,v),last)) : P last v := by
  have same := native_history body performed
  subst last
  exact stable.store h w v ((ProjectedAction.iff_run _ _ _).mp atom.store w value v (congrArg Prod.fst performed)) before

theorem stable_account : Stable Account := by
  refine ⟨fun _ _ before=>before,?_⟩
  intro h w v same before
  obtain ⟨ledger,before⟩:=before
  exact ⟨ledger,before.same_view (congrArg (fun s : WGStoreView=>StagedEntry.view {dev:=s.dev}) same)⟩

theorem stable_product : Stable CompleteProduct.Carrier :=
  ⟨fun _ _ before=>before.1,CompleteProduct.store_transport⟩

theorem stable_delete : Stable CompleteRunner.DeleteFrames.Entry :=
  ⟨fun _ _ before=>before.1.1,CompleteRunner.DeleteFrames.store⟩

abbrev Framing (P : List Event→World→Prop) (shape : Shape action) : Prop := ∀h w,P h w→Framed shape w h

theorem atom_bind {α β : Type} {body : Leanux.M α} (stable : Stable P) (atom : Atom body) {next : α→PrefixM Event β}
    (tail : ∀value,Shape (next value)) (later : ∀value,Framing P (tail value)) :
    Framing P (.bind atom.shape tail) := by
  intro h w before
  exact ⟨stable.account h w before,fun value u middle run=>later value middle u (stable.normal atom before run)⟩

theorem body_bind {α β : Type} {body : PrefixM Event α} {head : Shape body} {next : α→PrefixM Event β} (tail : ∀value,Shape (next value))
    (first : Framing P head) (later : ∀value,Framing Account (tail value)) : Framing P (.bind head tail) := by
  intro h w before
  have framed := first h w before
  exact ⟨framed,fun value u middle run=>later value middle u (framed.normal run)⟩

theorem atom_framing (stable : Stable P) (atom : Atom body) : Framing P atom.shape :=
  fun h w before=>stable.account h w before

theorem pure_framing (stable : Stable P) (value : α) : Framing P (.pure value) :=
  fun h w before=>stable.account h w before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment.Descriptor
