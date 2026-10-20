import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigSavedSource

/-! Configuration source witnesses expose creation, counted release, removal
and fixture sends. Native frames describe the fixed projection and allocation
companion; no point constructor assumes its desired account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TransmitSecurity CausalJournal Lifetimes RetirementSecurity
abbrev History := List Event

inductive NativeKind : Type 1 where
  | quiet {α : Type} (action : WG.M α) (frame : SameView StagedEntry.view action)
      (allocated : Preserves StackOwnership.Allocated action)
  | create (key : Key) (psk : Option Key)

def NativeKind.Result : NativeKind → Type
  | .quiet (α:=α) ..=>α
  | .create ..=>Except Int PeerId

def NativeKind.action (kind : NativeKind) : PrefixM Event kind.Result := match kind with
  | .quiet action ..=>liftWGObserver (liftWGPrefix action)
  | .create key psk=>liftWGObserver (liftWGPrefix (peerCreate key psk))

def pskUpdate (pid : PeerId) (psk : Option Key) : WGPrefix Event Unit := do
  let p ← liftWGPrefix (getPeer pid)
  liftWGPrefix (setPeer pid {p with presharedKey:=psk.getD []})

theorem psk_source (pid : PeerId) (psk : Option Key) :
    liftWGObserver (pskUpdate pid psk)=(ConfigSaved.read pid >>= fun p=>
      liftWGObserver (liftWGPrefix (setPeer pid {p with presharedKey:=psk.getD []}))) := by
  rw [pskUpdate,liftWGObserver_bind]
  rfl

inductive Family where
  | release (peer : Option PeerId)
  | remove (peer : Option PeerId)
  | removeAll
  | staging (trigger : FixtureEffects.Trigger) (pid : PeerId)
  | keepalive (trigger : FixtureEffects.Trigger) (pid : PeerId)

def Family.action : Family → PrefixM Event Unit
  | .release peer=>liftWGObserver (hooks.peerRelease peer)
  | .remove peer=>liftWGObserver (Driver.removeObserved hooks peer)
  | .removeAll=>liftWGObserver (Driver.removeAllObserved hooks)
  | .staging trigger pid=>FixtureScope.action trigger (Driver.stagingObserved hooks pid)
  | .keepalive trigger pid=>FixtureScope.action trigger (Driver.keepaliveObserved hooks pid)

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (token : NativeKind) : Shape token.action
  | child (family : Family) : Shape family.action
  | saved (pid : PeerId) (running : Bool) (interval : Nat) : Shape (ConfigSaved.action pid running interval)
  | psk (pid : PeerId) (psk : Option Key) : Shape (liftWGObserver (pskUpdate pid psk))
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀value,Shape (next value)) : Shape (body >>= next)

noncomputable def listShape (xs : List ι) (initial : σ)
    (body : ι → σ → PrefixM Event (ForInStep σ))
    (shapes : ∀value acc,Shape (body value acc)) : Shape (forIn xs initial body) :=
  List.rec (motive:=fun values=>∀acc,Shape (forIn values acc body))
    (fun acc=>.pure acc)
    (fun value rest ih acc=>(List.forIn_cons body value rest acc).symm ▸
      Shape.bind (shapes value acc) (fun decision=>match decision with
        | .done final=>.pure final
        | .yield next=>ih next)) xs initial

def observerBindShape (body : WGPrefix Event α) (next : α → WGPrefix Event β)
    (head : Shape (liftWGObserver body)) (tail : ∀value,Shape (liftWGObserver (next value))) :
    Shape (liftWGObserver (body >>= next)) :=
  (congrArg Shape (liftWGObserver_bind body next)).mpr (.bind head tail)

def quietShape (action : WG.M α) (frame : SameView StagedEntry.view action)
    (allocated : Preserves StackOwnership.Allocated action) : Shape (liftWGObserver (liftWGPrefix action)) :=
  .native (.quiet action frame allocated)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
