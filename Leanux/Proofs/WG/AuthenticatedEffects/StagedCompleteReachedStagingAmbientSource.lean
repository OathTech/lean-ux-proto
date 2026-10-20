import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingGetterSource

/-! Staging's non-store helpers factor through Ambient by source construction.
The component type has no WG state access; the equality retains all decisions,
hidden inputs, successful values and failures of the original helper. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.AmbientOnly
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity CausalJournal Points

inductive Shape : {α : Type} → WG.M α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | ambient (body : AmbientM α) : Shape (monadLift body)
  | bind {body : WG.M α} {next : α → WG.M β}
      (head : Shape body) (tail : ∀ value,Shape (next value)) : Shape (body >>= next)

def Shape.component {α : Type} {action : WG.M α} : Shape action → AmbientM α
  | .pure value => Pure.pure value
  | .ambient body => body
  | .bind head tail => head.component >>= fun value=>(tail value).component

theorem Shape.factor {α : Type} {action : WG.M α} (source : Shape action) : action=(monadLift source.component : WG.M α) := by
  induction source with
  | pure value => rfl
  | ambient body => rfl
  | bind head tail ihHead ihTail =>
      simp only [Shape.component,monadLift_bind]
      rw [←ihHead]
      congr 1
      funext value
      exact ihTail value

macro "staging_ambient_step" : tactic => `(tactic| first
  | exact Shape.pure _
  | exact Shape.ambient _
  | apply Shape.bind
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

inductive Kind : {α : Type} → Native α → Type 1 where
  | branch (site : Leanux.Decision) (value : Bool) : Kind (.branch site value)
  | compare (site : Leanux.Decision) (value : Bool) (left right : Int) : Kind (.compare site value left right)
  | age (birthday : Int64) : Kind (.age birthday)
  | ecn (packet : Packet) : Kind (.ecn packet)
  | incNotZero (count : Nat) : Kind (.incNotZero count)
  | inc (count : Nat) : Kind (.inc count)
  | notPending (pid : PeerId) : Kind (.notPending pid)
  | allocation : Kind .allocation
  | invariant (α : Type) : Kind (.invariant α)

noncomputable def Kind.source {α : Type} {token : Native α} (kind : Kind token) : Shape token.action := by
  cases kind with
  | branch site value => exact .ambient _
  | compare site value left right => exact .ambient _
  | age birthday =>
      unfold Native.action branchExpired birthdateTest
      simp only [hiddenClock64,branchCmp]
      repeat' staging_ambient_step
  | ecn packet =>
      unfold Native.action ipTunnelEcnEncap ipTunnelGetDsfield Packet.protocol
      simp only [unsupported]
      repeat' staging_ambient_step
  | incNotZero count =>
      unfold Native.action refcountIncNotZero
      simp only [branchCmp,unsupported]
      repeat' staging_ambient_step
  | inc count =>
      unfold Native.action refcountInc
      simp only [branchCmp,unsupported]
      repeat' staging_ambient_step
  | notPending pid => exact .pure ()
  | allocation => exact .ambient _
  | invariant α => exact .ambient _

theorem Kind.factor {α : Type} {token : Native α} (kind : Kind token) :
    token.action=(monadLift kind.source.component : WG.M α) := kind.source.factor

/-- Each original staging native is either a source-expanded getter, a
typed Ambient component, or one actual peer/key store write. -/
inductive Class : {α : Type} → Native α → Type 1 where
  | getter (source : Getter token) : Class token
  | ambient (source : Kind token) : Class token
  | peerWrite (pid : PeerId) (peer : Peer) : Class (.setPeer pid peer)
  | keyWrite (kid : KeypairId) (key : Keypair) : Class (.setKey kid key)

def classify (token : Native α) : Class token := by
  cases token with
  | peer pid => exact .getter (.peer pid)
  | device => exact .getter .device
  | key kid => exact .getter (.key kid)
  | owner kid => exact .getter (.owner kid)
  | setPeer pid peer => exact .peerWrite pid peer
  | setKey kid key => exact .keyWrite kid key
  | branch site value => exact .ambient (.branch site value)
  | compare site value left right => exact .ambient (.compare site value left right)
  | age birthday => exact .ambient (.age birthday)
  | ecn packet => exact .ambient (.ecn packet)
  | incNotZero count => exact .ambient (.incNotZero count)
  | inc count => exact .ambient (.inc count)
  | notPending pid => exact .ambient (.notPending pid)
  | allocation => exact .ambient .allocation
  | invariant α => exact .ambient (.invariant α)

theorem peer_write_source (pid : PeerId) (peer : Peer) :
    Native.action (.setPeer pid peer) = (modify fun w : WGWorld=>
      {w with dev:=w.dev.map fun d=>{d with peers:=d.peers.insert pid peer}}) := rfl

theorem key_write_source (kid : KeypairId) (key : Keypair) :
    Native.action (.setKey kid key) = (modify fun w : WGWorld=>
      {w with dev:=w.dev.map fun d=>{d with keypairs:=d.keypairs.insert kid key}}) := rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.AmbientOnly
