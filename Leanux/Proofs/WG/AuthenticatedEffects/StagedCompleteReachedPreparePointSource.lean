import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDecryptSource

/-! Fixed source witnesses for decrypt preparation. Access atoms retain the
original lifetime observer; their native mutation and following receipt are
separate points. Focus and decrypt capture preserve their actual input state.
There is no arbitrary factor-equation constructor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal

inductive Access : {E α : Type} → WGPrefix E α → Type 1 where
  | readPeer (pid : PeerId) : Access (Peers.getPeerPrefix pid)
  | writePeer (pid : PeerId) (p : Peer) : Access (Peers.setPeerPrefix pid p)
  | readKey (id : KeypairId) : Access (getKeypairPrefix id)
  | writeKey (id : KeypairId) (k : Keypair) : Access (setKeypairPrefix id k)
  | readRx (id : SkbId) : Access (getRxSkbPrefix id)
  | writeRx (id : SkbId) (p : RxPacket) : Access (writeRxSkbPrefix id p)

def Access.native : {E α : Type} → {body : WGPrefix E α} → Access body → WG.M α
  | _,_,_,.readPeer pid => getPeer pid
  | _,_,_,.writePeer pid p => setPeer pid p
  | _,_,_,.readKey id => getKeypair id
  | _,_,_,.writeKey id k => setKeypair id k
  | _,_,_,.readRx id => getRxSkb id
  | _,_,_,.writeRx id p => modifyDev fun d => {d with rxSkbs:=d.rxSkbs.insert id p}

def Access.events : {E α : Type} → {body : WGPrefix E α} →
    Access body → WGWorld → α → List E
  | _,_,_,.readPeer pid,_,p => [.read pid p.internalId]
  | _,_,_,.writePeer pid p,w,_ => if w.dev.isSome then [.write pid p.internalId] else []
  | _,_,_,.readKey id,_,k => [.keypair (.read id k.internalId)]
  | _,_,_,.writeKey id k,w,_ => if w.dev.isSome then [.keypair (.write id k.internalId)] else []
  | _,_,_,.readRx id,w,_ => [.packet (.read (.inr id) (packetStamp w id))]
  | _,_,_,.writeRx id _,w,_ => if w.dev.isSome then [.packet (.write (.inr id) (packetStamp w id))] else []

/-- The native read/write is completed before its original access receipt.
All writers here are total; their absent-device branch emits no event. -/
theorem Access.run {E α : Type} {body : WGPrefix E α}
    (token : Access body) (w : WGWorld) (a : Ambient) (h : List E) :
    runWGPrefix body w a h = match (token.native.run w).run a with
      | .error reason => (.error reason,h)
      | .ok ((value,v),b) => (.ok ((value,v),b),h ++ token.events w value) := by
  cases token with
  | readPeer pid =>
      change runStatePrefix _ w a h = _
      rw [Peers.getPeerPrefix_run]
      simp only [Access.native,Access.events,StateT.run]
      cases run : (getPeer pid) w a with
      | error reason => rfl
      | ok out => obtain ⟨⟨value,v⟩,b⟩:=out; rfl
  | readKey id =>
      change runStatePrefix _ w a h = _
      rw [getKeypairPrefix_run]
      simp only [Access.native,Access.events,StateT.run]
      cases run : (getKeypair id) w a with
      | error reason => rfl
      | ok out => obtain ⟨⟨value,v⟩,b⟩:=out; rfl
  | readRx id =>
      change runStatePrefix _ w a h = _
      rw [getRxSkbPrefix_run]
      simp only [Access.native,Access.events,StateT.run]
      cases run : (getRxSkb id) w a with
      | error reason => rfl
      | ok out => obtain ⟨⟨value,v⟩,b⟩:=out; rfl
  | writePeer pid p =>
      change runStatePrefix _ w a h = _
      rw [Peers.setPeerPrefix_run]
      change (_,if w.dev.isSome then _ else _) = (_,h ++ if w.dev.isSome then _ else _)
      split <;> simp_all only [List.append_nil] <;> rfl
  | writeKey id k =>
      change runStatePrefix _ w a h = _
      rw [setKeypairPrefix_run]
      change (_,if w.dev.isSome then _ else _) = (_,h ++ if w.dev.isSome then _ else _)
      split <;> simp_all only [List.append_nil] <;> rfl
  | writeRx id p =>
      change runStatePrefix _ w a h = _
      rw [writeRxSkbPrefix_run]
      change (_,if w.dev.isSome then _ else _) = (_,h ++ if w.dev.isSome then _ else _)
      split <;> simp_all only [List.append_nil] <;> rfl

inductive Shape : {E α : Type} → WGPrefix E α → Type 1 where
  | pure (value : α) : Shape (pure value : WGPrefix E α)
  | quiet (body : WG.M α) (frame : SameView StagedEntry.view body) : Shape (liftWGPrefix body : WGPrefix E α)
  | access {E α : Type} {body : WGPrefix E α} (token : Access body) : Shape body
  | bind {body : WGPrefix E α} {next : α → WGPrefix E β}
      (head : Shape body) (tail : ∀ value,Shape (next value)) : Shape (body >>= next)
  | focus {E F α : Type} {action : WGPrefix E α} (encode : E → F) (decode : F → Option E)
      (inverse : ∀ event,decode (encode event)=some event) (body : Shape action) :
      Shape (focusStatePrefix encode decode action)
  | receipt {E α : Type} {action : WGPrefix E α} (body : Shape action) (record : WGRunWitness α → E) :
      Shape (receiptWGObserved action record)

theorem Shape.appends {E α : Type} {action : WGPrefix E α} (shape : Shape action) : StateAppends action := by
  induction shape with
  | pure value => exact StateAppends.pure value
  | quiet body frame => exact StateAppends.lift body
  | access token =>
      intro w a h
      change ∃suffix,(runWGPrefix _ w a h).2=h++suffix
      rw [token.run]
      cases outcome : (token.native.run w).run a with
      | error reason => exact ⟨[],by simp⟩
      | ok pair => rcases pair with ⟨⟨value,v⟩,b⟩; exact ⟨_,rfl⟩
  | bind head tail ihHead ihTail => exact StateAppends.bind ihHead ihTail
  | focus encode decode inverse body ih => exact StateAppends.focus encode decode _
  | receipt body record ih => exact ih.receiptWGObserved record

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Prepare.Points
