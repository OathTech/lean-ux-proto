import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPrimitiveKeyCoverage

/-! Native queued-initiation source witnesses. A cached peer setter is paired
with its original getter and an ambient-only guard; the guard cannot alter
the peer whose metadata is written. Source points expose both accesses. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive.QueueNative
open Leanux Leanux.WG Leanux.Proofs.Logged

def guardedUpdate (pid : PeerId) (f : Peer → Peer) (guardBody : Peer → AmbientM Unit) : WG.M Unit := do
  let peer ← getPeer pid
  monadLift (guardBody peer)
  setPeer pid (f peer)

abbrev Fields (f : Peer → Peer) :=
  ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged ∧ (f p).txQueue = p.txQueue

inductive Shape : {α : Type} → WG.M α → Type 1 where
  | quiet (source : KeyShape action) : Shape action
  | update (pid : PeerId) (f : Peer → Peer) (guardBody : Peer → AmbientM Unit)
      (fields : Fields f) : Shape (guardedUpdate pid f guardBody)
  | age (site : Decision) (birth : Int64) (limit : Nat) (test : Bool → Bool) :
      Shape (branchExpired site birth limit test)
  | bind {body : WG.M α} {next : α → WG.M β}
      (head : Shape body) (tail : ∀ value,Shape (next value)) : Shape (body >>= next)

def pureShape (value : α) : Shape (pure value) := .quiet (.pure value)
def branchShape (site : Decision) (flag : Bool) : Shape (branch site flag) :=
  .quiet (StagingPrimitive.branchShape site flag)
def readShape (pid : PeerId) : Shape (getPeer pid) := .quiet (peerShape pid)
def updateShape (pid : PeerId) (f : Peer → Peer) (fields : Fields f) :
    Shape (do setPeer pid (f (← getPeer pid))) := by
  simpa only [guardedUpdate,show (monadLift (pure () : AmbientM Unit) : WG.M Unit) = pure () from rfl,pure_bind]
    using Shape.update pid f (fun _=>pure ()) fields

def updateThenShape (pid : PeerId) (f : Peer → Peer) (next : Unit → WG.M α)
    (fields : Fields f) (tail : ∀ value,Shape (next value)) :
    Shape (getPeer pid >>= fun peer=>setPeer pid (f peer) >>= next) := by
  rw [← bind_assoc]
  exact .bind (updateShape pid f fields) tail

theorem acquire_factor (pid : PeerId) :
    peerGet pid = guardedUpdate pid (fun p=>{p with refcount:=p.refcount+1})
      (fun p=>refcountInc p.refcount) := by
  unfold peerGet guardedUpdate requireNotPending
  simp only [pure_bind]
  congr 1
  funext peer
  congr 1
  simp only [refcountInc,branch,branchCmp,unsupported,monadLift_self,
    monadLift_bind,monadLift_pure,apply_ite]

def acquireShape (pid : PeerId) : Shape (peerGet pid) := by
  rw [acquire_factor]
  exact .update pid _ _ (fun _=>⟨rfl,rfl,rfl⟩)

def readyShape (pid : PeerId) : Shape (Queued.readyPrefix pid) := by
  unfold Queued.readyPrefix
  repeat' first
    | exact updateShape _ _ (fun _=>⟨rfl,rfl,rfl⟩)
    | (apply updateThenShape; · intro p; exact ⟨rfl,rfl,rfl⟩)
    | exact branchShape _ _
    | exact readShape _
    | exact Shape.age _ _ _ _
    | exact pureShape _
    | apply Shape.bind
    | intro value
    | split

def borrowedShape (pid : PeerId) (pending : Bool) : Shape (Queued.borrowedDecision pid pending) := by
  unfold Queued.borrowedDecision
  exact .bind (acquireShape pid) fun _=>
    .bind (.quiet (.atom (.ambient (AmbientM.peekQueuedUnit .sendWorker pid)))) fun selected=>
      .bind (branchShape .queuedAlreadyQueued (pending && !selected)) fun result=>pureShape (some result)

def decisionShape (pid : PeerId) : Shape (Queued.decisionPrefix pid) := by
  unfold Queued.decisionPrefix
  apply Shape.bind (readyShape pid)
  intro ready
  cases ready with
  | none=>exact pureShape none
  | some peer=>exact borrowedShape pid peer.handshakePending

def installShape (pid : PeerId) : Shape (Queued.install pid) := by
  unfold Queued.install
  exact updateThenShape pid _ _ (fun _=>⟨rfl,rfl,rfl⟩) fun _=>
    .quiet (.atom (.ambient (AmbientM.recordQueued .sendWorker pid)))

inductive Point : {α : Type} → {action : WG.M α} → Shape action →
    WGWorld → Ambient → WGWorld → Ambient → WG.M α → Type 1 where
  | entry (shape : Shape action) : Point shape w a w a action
  | returned (shape : Shape action) (run : (action.run w).run a=.ok ((value,v),b)) :
      Point shape w a v b (pure value)
  | quiet (source : KeyShape action) (point : KeyPoint source w a leaf v b rest) :
      Point (.quiet source) w a v b rest
  | reading (fields : Fields f)
      (point : KeyPoint (peerShape pid) w a leaf v b rest) :
      Point (.update pid f guardBody fields) w a v b (do
        let peer ← rest
        monadLift (guardBody peer)
        setPeer pid (f peer))
  | guarded (fields : Fields f)
      (read : ((getPeer pid).run w).run a=.ok ((peer,u),c))
      (checked : (guardBody peer).run c=.ok ((),b)) :
      Point (.update pid f guardBody fields) w a u b (setPeer pid (f peer))
  | left {body : WG.M α} {next : α → WG.M β} {head : Shape body}
      (tail : ∀ value,Shape (next value)) (point : Point head w a v b rest) :
      Point (.bind head tail) w a v b (rest >>= next)
  | right {body : WG.M α} {next : α → WG.M β} (head : Shape body)
      (tail : ∀ value,Shape (next value))
      (leading : (body.run w).run a=.ok ((value,u),c))
      (point : Point (tail value) u c v b rest) : Point (.bind head tail) w a v b rest

theorem Point.residual {action : WG.M α} {shape : Shape action}
    (point : Point shape w a v b rest) : (action.run w).run a=(rest.run v).run b := by
  induction point with
  | entry=>rfl
  | returned shape run=>exact run
  | quiet source point=>exact point.residual
  | reading fields point=>
    simp only [guardedUpdate,StateT.run_bind,point.residual]
  | guarded fields read checked=>
    simp [guardedUpdate,StateT.run_bind,read,checked]
  | left tail point ih=>simp only [StateT.run_bind]; rw [ih]
  | right head tail leading point ih=>simp only [StateT.run_bind]; rw [leading]; exact ih

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive.QueueNative
