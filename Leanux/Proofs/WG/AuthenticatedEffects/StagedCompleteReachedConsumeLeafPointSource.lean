import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumePointNapi
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReceiveHelperCanonical

/-! Fixed receive helper atoms. Peer updates are paired with their own native
read; the metadata constraint excludes staged queues and packet ownership. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

abbrev History := List Event
abbrev Result (α : Type) := Except Stop (α × World)
abbrev wg (action : WG.M α) : PrefixM Event α := Points.wg action

inductive BaseNative : {α : Type} → PrefixM Event α → Type 1 where
  | basic (token : Points.Native action) : BaseNative action
  | ambient (body : AmbientM α) : BaseNative (wg (monadLift body : WG.M α))
  | world : BaseNative (wg (get : WG.M WGWorld))
  | device : BaseNative (wg getDev)
  | update (pid : PeerId) (f : Peer → Peer)
      (fields : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged ∧ (f p).txQueue = p.txQueue) :
      BaseNative (wg (do setPeer pid (f (← getPeer pid))))
  | dereference (owner : IndexOwner) : BaseNative (wg owner.peerDeref)
  | unhash (owner : IndexOwner) : BaseNative (wg (liftIndex (indexRemove owner)))
  | eraseKey (kid : KeypairId) : BaseNative (wg (modifyDev fun d => {d with keypairs := d.keypairs.erase kid}))
  | endian (bits : Nat) : BaseNative (wg (swapEndian bits))

def historyRead : PrefixM Event History := fun w => ExceptT.mk fun h => (.ok (h,w),h)

inductive Native where
  | metadata (body : WG.M α) (source : PeerMetadata.Shape body)
  | base {α : Type} {action : PrefixM Event α} (token : BaseNative action)
  | find (root : Option NodeId) (bits key : Nat)
  | node (id : NodeId)
  | acquire (peer : Option PeerId)
  | change (f : WGWorld → WGWorld) (same : ∀ w, StagedEntry.view (f w) = StagedEntry.view w)
  | failure (reason : Stop)
  | history
  | armed (receipt : TimerEffects.Arm Context)

def Native.Result : Native → Type
  | @Native.metadata α _ _ => α
  | @Native.base α _ _ => α
  | .find .. => Option NodeId
  | .node .. => AipNode
  | .acquire .. => Option PeerId
  | .history => History
  | .change .. | .failure .. | .armed .. => Unit

def Native.action (token : Native) : PrefixM Event token.Result := match token with
  | .metadata body _ => wg body
  | @Native.base _ action _ => action
  | .find root bits key => wg (liftAip (findNode root bits key))
  | .node id => wg (liftAip (getNode id))
  | .acquire peer => wg (peerGetMaybeZero peer)
  | .change f _ => wg (modify f)
  | .failure reason => wg (throw reason)
  | .history => historyRead
  | .armed receipt => emitPrefix (.armed receipt)

theorem acquire_observed_remaining {w : World} (h : History)
    (point : PeerAcquire.Point peer w.wg w.ambient v b) :
    ∃ remaining : PrefixM Event (Option PeerId), runPrefix (wg (peerGetMaybeZero peer)) w h =
      runPrefix remaining {w with wg:=v,ambient:=b} h := by
  obtain ⟨rest,same⟩ := point.remaining
  refine ⟨liftWGObserver (liftWGPrefix rest),?_⟩
  simp only [wg,Points.wg,liftWGObserver_run,runWGPrefix_lift,same]

noncomputable def acquireRemainder {w : World} (h : History)
    (point : PeerAcquire.Point peer w.wg w.ambient v b) : PrefixM Event (Option PeerId) :=
  Classical.choose (acquire_observed_remaining h point)

theorem acquireRemainder_run {w : World} (h : History)
    (point : PeerAcquire.Point peer w.wg w.ambient v b) :
    runPrefix (wg (peerGetMaybeZero peer)) w h =
      runPrefix (acquireRemainder h point) {w with wg:=v,ambient:=b} h :=
  Classical.choose_spec (acquire_observed_remaining h point)

inductive Child where
  | wheel (pid : PeerId) (timer : PeerTimer) (expires clock : UInt64) (unit : Option Nat)
  | arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (clock : Option UInt64)

def Child.Result (_ : Child) : Type := Unit

def Child.action (token : Child) : PrefixM Event token.Result := match token with
  | .arm pid timer delay clock => liftWGObserver (effects.arm pid timer delay clock)
  | .wheel pid timer expires clock unit => wg (placeOnWheel pid timer expires clock unit)

inductive Label where
  | endpoint (pid : PeerId) (endpoint : Endpoint)
  | cache (pid : PeerId)
  | keyRelease (kid : Option KeypairId) (unreferenceNow : Bool)
  | lookup (protocol : Nat) (bytes : List UInt8)
  | lookupNode (root : Option NodeId) (bits key : Nat)
  | handshakeTimer (pid : PeerId)
  | authenticated (pid : PeerId)
  | traversal (pid : PeerId)
  | received (pid : PeerId)

inductive Failure : {α : Type} → PrefixM Event α → Type 1 where
  | wgThrow (reason : Stop) : Failure (wg (throw reason : WG.M α))
  | invariant (message : String) : Failure (liftPrefix (Leanux.invariant message : Leanux.M α))
  | unsupported (message : String) : Failure (liftPrefix (Leanux.unsupported message : Leanux.M α))
  | excluded (message : String) : Failure (liftPrefix (Leanux.Env.Stack.excluded message))
  | wgInvariant (message : String) : Failure (wg (invariant message : WG.M α))
  | wgUnsupported (message : String) : Failure (wg (unsupported message : WG.M α))

theorem Failure.run (failure : Failure action) (w : World) (h : History) :
    ∃ reason, runPrefix action w h = (.error reason,h) := by
  cases failure <;> exact ⟨_,rfl⟩

inductive Shape : {α : Type} → PrefixM Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (token : Native) : Shape token.action
  | child (token : Child) : Shape token.action
  | failed {α β : Type} {body : PrefixM Event α} (failure : Failure body) (next : α → PrefixM Event β) : Shape (body >>= next)
  | bind {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value)) : Shape (body >>= next)
  | marked (label : Label) (body : Shape action) : Shape action

noncomputable def conditionalShape (test : Prop) [Decidable test]
    {left right : PrefixM Event α} (yes : test → Shape left) (no : ¬test → Shape right) :
    Shape (if test then left else right) := by
  split
  · exact yes ‹_›
  · exact no ‹_›

noncomputable def listShape (xs : List α) (initial : σ)
    (body : α → σ → PrefixM Event (ForInStep σ)) (shapes : ∀ item acc, Shape (body item acc)) :
    Shape (forIn xs initial body) :=
  List.rec (motive := fun items => ∀ acc, Shape (forIn items acc body))
    (fun acc => .pure acc)
    (fun item rest ih acc => (List.forIn_cons body item rest acc).symm ▸
      Shape.bind (shapes item acc) (fun decision => match decision with
        | .done final => .pure final
        | .yield next => ih next)) xs initial

noncomputable def forMShape (xs : List α) (body : α → PrefixM Event Unit)
    (shapes : ∀ item, Shape (body item)) : Shape (xs.forM body) := by
  induction xs with
  | nil => exact .pure ()
  | cons item rest ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact .bind (shapes item) (fun _ => ih)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
