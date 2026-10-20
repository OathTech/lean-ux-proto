import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDeviceCreationFrames

/-! A fixed source witness, not an existential factorization, determines
lifecycle points. Native tokens carry concrete projection frames. Transition
inputs are phase-specific: setup, newlink, destructor check and reset cannot
be treated as ordinary allocation-preserving frames. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity
abbrev Result (α : Type) := Except Stop (α × World)

inductive Native : {α : Type} → PrefixM Event α → Type 1 where
  | quiet (action : Leanux.M α)
      (frame : SameView (fun w : World => StagedEntry.view w.wg) action) : Native (liftPrefix action)
  | setup : Native (liftPrefix (liftWG wgSetup))
  | newlink : Native (liftPrefix (liftWG wgNewlink))
  | erase : Native (liftPrefix (liftWG (_root_.modify fun w : WGWorld => {w with dev:=none})))
  | check : Native (liftPrefix (liftWG TxWork.Destruct.check))

inductive Family where
  | staging (pid : PeerId)
  | keepalive (pid : PeerId)
  | drain (upTo : Option PeerId)
  | purge (pid : PeerId)
  | release (peer : Option PeerId)

def Family.Result (_ : Family) : Type := Unit

def Family.action (family : Family) : PrefixM Event family.Result := match family with
  | .staging pid => liftWGObserver (FixtureEffects.runWith (Driver.fixtureOps hooks) (.interfaceOpen pid .staging) (Driver.stagingObserved hooks pid))
  | .keepalive pid => liftWGObserver (FixtureEffects.runWith (Driver.fixtureOps hooks) (.interfaceOpen pid .keepalive) (Driver.keepaliveObserved hooks pid))
  | .drain upTo => liftWGObserver (Driver.sendDrainObserved hooks upTo)
  | .purge pid => liftWGObserver (hooks.stagedPurge pid)
  | .release peer => liftWGObserver (hooks.peerRelease peer)

inductive Child : {α : Type} → PrefixM Event α → Type 1 where
  | family (source : Family) : Child source.action

inductive Label where
  | create | newlink | opened | up | down | stop | removeAll | prepare | destruct | reset
  | envUp | envDown | envDelete | dispatchCreate | dispatchDelete
  | peer (pid : PeerId)
  | timers (pid : PeerId)
  | list

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (token : Native action) : Shape action
  | child (token : Child action) : Shape action
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value)) : Shape (body >>= next)
  | marked (label : Label) (body : Shape action) : Shape action

noncomputable def listShape (xs : List ι) (initial : σ)
    (body : ι → σ → PrefixM Event (ForInStep σ))
    (shapes : ∀ value acc, Shape (body value acc)) : Shape (forIn xs initial body) :=
  List.rec (motive := fun values => ∀ acc, Shape (forIn values acc body))
    (fun acc => .pure acc)
    (fun value rest ih acc => (List.forIn_cons body value rest acc).symm ▸
      Shape.bind (shapes value acc) (fun decision => match decision with
        | .done final => .pure final
        | .yield next => ih next)) xs initial

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
