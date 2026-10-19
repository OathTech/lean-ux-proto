import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecycleEnvironmentCoverage
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchPointCoverage

/-! Four dispatch children are filled by the concrete canonical lifecycle
wrappers. All other dispatch families retain their independent contracts.
No whole lifecycle, dispatch or deletion-frame premise is introduced. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal Points

/-- Only the four original lifecycle caller families are refined. -/
def joined (life : ChildPoints) (other : Dispatch.Points.ChildPoints) : Dispatch.Points.ChildPoints :=
  fun _ _ token w h u middle=>match token with
    | .family .create => RootPoints life .create w h u middle
    | .family .delete => RootPoints life .delete w h u middle
    | .family .open => RootPoints life .open w h u middle
    | .family .down => RootPoints life .down w h u middle
    | token => other _ _ token w h u middle

variable {native inside : ChildPoints} {otherNative otherInside : Dispatch.Points.ChildPoints}
variable {Good : List Event→World→Prop}

noncomputable def create_contract (accountGood : ∀h w,Account h w→Good h w)
    (children : ChildContracts native inside Good) :
    Dispatch.Points.ChildSourceContract (joined native otherNative) (joined inside otherInside) Good (.family .create) where
  remainder := remainder .create children
  continuation := fun _ _ _ _ point=>remainder_run .create children point
  coverage := fun _ _ _ _ point=>root_coverage .create children point
  safe := fun _ _ _ _ before point=>root_safe .create accountGood children before point

noncomputable def delete_contract (accountGood : ∀h w,Account h w→Good h w)
    (children : ChildContracts native inside Good) :
    Dispatch.Points.ChildSourceContract (joined native otherNative) (joined inside otherInside) Good (.family .delete) where
  remainder := remainder .delete children
  continuation := fun _ _ _ _ point=>remainder_run .delete children point
  coverage := fun _ _ _ _ point=>root_coverage .delete children point
  safe := fun _ _ _ _ before point=>root_safe .delete accountGood children before.1 point

noncomputable def open_contract (accountGood : ∀h w,Account h w→Good h w)
    (children : ChildContracts native inside Good) :
    Dispatch.Points.ChildSourceContract (joined native otherNative) (joined inside otherInside) Good (.family .open) where
  remainder := remainder .open children
  continuation := fun _ _ _ _ point=>remainder_run .open children point
  coverage := fun _ _ _ _ point=>root_coverage .open children point
  safe := fun _ _ _ _ before point=>root_safe .open accountGood children before point

noncomputable def down_contract (accountGood : ∀h w,Account h w→Good h w)
    (children : ChildContracts native inside Good) :
    Dispatch.Points.ChildSourceContract (joined native otherNative) (joined inside otherInside) Good (.family .down) where
  remainder := remainder .down children
  continuation := fun _ _ _ _ point=>remainder_run .down children point
  coverage := fun _ _ _ _ point=>root_coverage .down children point
  safe := fun _ _ _ _ before point=>root_safe .down accountGood children before point

/-- Exactly the ten unrelated source families remain. Lifecycle children do
not occur among these inputs. -/
structure OtherContracts (native inside : Dispatch.Points.ChildPoints) (Good : List Event→World→Prop) where
  config : ∀attrs,Dispatch.Points.ChildSourceContract native inside Good (.family (.config attrs))
  transmit : ∀family addr payload opts,Dispatch.Points.ChildSourceContract native inside Good (.family (.transmit family addr payload opts))
  receive : ∀family port message tos ll dest,Dispatch.Points.ChildSourceContract native inside Good (.family (.receive family port message tos ll dest))
  flood : ∀count port family messages,Dispatch.Points.ChildSourceContract native inside Good (.family (.flood count port family messages))
  batch : ∀items,Dispatch.Points.ChildSourceContract native inside Good (.family (.batch items))
  dumpDevice : ∀ref,Dispatch.Points.ChildSourceContract native inside Good (.family (.dumpDevice ref))
  dumpStart : ∀fd ref,Dispatch.Points.ChildSourceContract native inside Good (.family (.dumpStart fd ref))
  dumpReceive : ∀fd,Dispatch.Points.ChildSourceContract native inside Good (.family (.dumpReceive fd))
  idle : Dispatch.Points.ChildSourceContract native inside Good (.family .idle)
  delivery : Dispatch.Points.ChildSourceContract native inside Good (.family .delivery)

/-- Change only point relations at this same fixed child action. -/
noncomputable def retain_contract {α : Type} {action : PrefixM Event α} {token : Dispatch.Points.Child action}
    (old : Dispatch.Points.ChildSourceContract otherNative otherInside Good token)
    (nativeSame : ∀w h u middle,joined native otherNative _ _ token w h u middle ↔ otherNative _ _ token w h u middle)
    (insideSame : ∀w h u middle,joined inside otherInside _ _ token w h u middle ↔ otherInside _ _ token w h u middle) :
    Dispatch.Points.ChildSourceContract (joined native otherNative) (joined inside otherInside) Good token where
  remainder := fun w h u middle point=>old.remainder w h u middle ((nativeSame w h u middle).mp point)
  continuation := fun w h u middle point=>old.continuation w h u middle ((nativeSame w h u middle).mp point)
  coverage := fun w h u middle point=>(insideSame w h u middle).mpr
    (old.coverage w h u middle ((nativeSame w h u middle).mp point))
  safe := fun w h u middle before point=>old.safe w h u middle before ((insideSame w h u middle).mp point)

noncomputable def dispatch_contracts (accountGood : ∀h w,Account h w→Good h w)
    (children : ChildContracts native inside Good) (others : OtherContracts otherNative otherInside Good) :
    Dispatch.Points.ChildContracts (joined native otherNative) (joined inside otherInside) Good where
  create := create_contract accountGood children
  delete := delete_contract accountGood children
  openDevice := open_contract accountGood children
  down := down_contract accountGood children
  config := fun attrs=>retain_contract (others.config attrs) (fun _ _ _ _=>Iff.rfl) (fun _ _ _ _=>Iff.rfl)
  transmit := fun family addr payload opts=>retain_contract (others.transmit family addr payload opts) (fun _ _ _ _=>Iff.rfl) (fun _ _ _ _=>Iff.rfl)
  receive := fun family port message tos ll dest=>retain_contract (others.receive family port message tos ll dest) (fun _ _ _ _=>Iff.rfl) (fun _ _ _ _=>Iff.rfl)
  flood := fun count port family messages=>retain_contract (others.flood count port family messages) (fun _ _ _ _=>Iff.rfl) (fun _ _ _ _=>Iff.rfl)
  batch := fun items=>retain_contract (others.batch items) (fun _ _ _ _=>Iff.rfl) (fun _ _ _ _=>Iff.rfl)
  dumpDevice := fun ref=>retain_contract (others.dumpDevice ref) (fun _ _ _ _=>Iff.rfl) (fun _ _ _ _=>Iff.rfl)
  dumpStart := fun fd ref=>retain_contract (others.dumpStart fd ref) (fun _ _ _ _=>Iff.rfl) (fun _ _ _ _=>Iff.rfl)
  dumpReceive := fun fd=>retain_contract (others.dumpReceive fd) (fun _ _ _ _=>Iff.rfl) (fun _ _ _ _=>Iff.rfl)
  idle := retain_contract others.idle (fun _ _ _ _=>Iff.rfl) (fun _ _ _ _=>Iff.rfl)
  delivery := retain_contract others.delivery (fun _ _ _ _=>Iff.rfl) (fun _ _ _ _=>Iff.rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment
