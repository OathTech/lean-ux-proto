import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWheelPointConsume
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductWork
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSendDrain

/-! Fixed work-service source vocabulary. The only open bodies are the actual
flushed protocol sender and peer repayment. Canonical Leaf witnesses retain
key-release interiors; no whole queued/service body is a child. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal
open RetirementSecurity
abbrev History := List Event
abbrev Result (α : Type) := Except Stop (α × World)
abbrev wg (body : WG.M α) : PrefixM Event α := Consume.Leaf.wg body
abbrev Carrier := Consume.Leaf.Carrier
abbrev Checked (action : PrefixM Event α) := Consume.Leaf.Checked action
abbrev Failure (action : PrefixM Event α) := Consume.Leaf.Failure action

inductive Native where
  | ambient {α : Type} (body : AmbientM α)
  | change (f : Device → Device)
      (same : ∀ w, StagedEntry.view {w with dev := w.dev.map f} = StagedEntry.view w)
  | acquire (pid : PeerId)
  | expired (site : Decision) (birth : Int64) (limit : Nat) (test : Bool → Bool)
  | queued (receipt : TimerEffects.Queued Context)

def Native.Result : Native → Type
  | @Native.ambient α _ => α
  | .expired .. => Bool
  | _ => Unit

def Native.action (token : Native) : PrefixM Event token.Result := match token with
  | .ambient body => liftPrefix (Leanux.liftAmbient body)
  | .change f _ => wg (modifyDev f)
  | .acquire pid => wg (peerGet pid)
  | .expired site birth limit test => wg (branchExpired site birth limit test)
  | .queued receipt => emitPrefix (.queued receipt)

inductive Child where
  | release (peer : Option PeerId)
  | flushedSend (pid : PeerId)

def Child.action : Child → PrefixM Event Unit
  | .release peer => liftWGObserver (peerRelease peer)
  | .flushedSend pid => liftWGObserver (CausalJournal.flushedSend pid)

inductive Label where
  | queued (pid : PeerId) (retry : Bool)
  | clear (pid : PeerId)
  | flushedClear (pid : PeerId)
  | scheduledSend
  | scheduledClear
  | drain (upTo : Option PeerId)

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (token : Native) : Shape token.action
  | leaf (source : Consume.Leaf.Shape action) : Shape action
  | child (token : Child) : Shape token.action
  | failed {α β : Type} {body : PrefixM Event α} (failure : Failure body) (next : α → PrefixM Event β) :
      Shape (body >>= next)
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value)) : Shape (body >>= next)
  | marked (label : Label) (shape : Shape action) : Shape action

noncomputable def conditionalShape (test : Prop) [Decidable test]
    {left right : PrefixM Event α} (yes : test → Shape left) (no : ¬test → Shape right) :
    Shape (if test then left else right) := by split; exact yes ‹_›; exact no ‹_›

noncomputable def listShape (xs : List α) (initial : σ)
    (body : α → σ → PrefixM Event (ForInStep σ)) (shapes : ∀ item acc, Shape (body item acc)) :
    Shape (forIn xs initial body) :=
  List.rec (motive := fun items => ∀ acc, Shape (forIn items acc body))
    (fun acc => .pure acc)
    (fun item rest ih acc => (List.forIn_cons body item rest acc).symm ▸
      Shape.bind (shapes item acc) (fun decision => match decision with
        | .done final => .pure final
        | .yield next => ih next)) xs initial

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
