import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingInteriorObserver
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingAllocation

/-! Fixed source witnesses for staging. Constructors name original native
calls or finite child boundaries; a caller cannot insert an arbitrary
factorization. Captures retain their original before-world and clock. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity CausalJournal
open Staged.Obligations HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000

abbrev History := List Event
abbrev Result (α : Type) := Except Stop ((α × WGWorld) × Ambient)

inductive Native : Type → Type 1 where
  | peer (pid : PeerId) : Native Peer
  | setPeer (pid : PeerId) (peer : Peer) : Native Unit
  | device : Native Device
  | key (kid : KeypairId) : Native Keypair
  | setKey (kid : KeypairId) (key : Keypair) : Native Unit
  | branch (site : Leanux.Decision) (value : Bool) : Native Bool
  | compare (site : Leanux.Decision) (value : Bool) (left right : Int) : Native Bool
  | age (birthday : Int64) : Native Bool
  | ecn (packet : Packet) : Native Nat
  | incNotZero (count : Nat) : Native Bool
  | inc (count : Nat) : Native Unit
  | notPending (pid : PeerId) : Native Unit
  | owner (kid : KeypairId) : Native PeerId
  | allocation : Native Bool
  | invariant (α : Type) : Native α

def Native.action : Native α → WG.M α
  | .peer pid=>getPeer pid
  | .setPeer pid value=>WG.setPeer pid value
  | .device=>getDev
  | .key kid=>getKeypair kid
  | .setKey kid value=>setKeypair kid value
  | .branch site value=>Leanux.branch site value
  | .compare site value left right=>branchCmp site value left right
  | .age birthday=>branchExpired .stagedBirthdateExpired birthday REJECT_AFTER_TIME
  | .ecn packet=>ipTunnelEcnEncap packet
  | .incNotZero count=>refcountIncNotZero count
  | .inc count=>refcountInc count
  | .notPending pid=>requireNotPending pid "a reference count the handshake worker also changes"
  | .owner kid=>IndexOwner.peerDeref (.keypair kid)
  | .allocation=>hiddenAlloc .keepaliveSkb
  | .invariant _=>Leanux.invariant "unreachable"

/-- These are the finite deeper obligations. The source witness never treats
allocation, counted release or publication as a passive native frame. -/
inductive Child : {α : Type} → WGPrefix Event α → Type 1 where
  | reserve (kid : KeypairId) : Child (state (Journal.reserve kid))
  | repayment (key : Option KeypairId) : Child (liftWGPrefix (keypairPut key false))
  | queued (pid : PeerId) : Child (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false)
  | allocate (packets : List DataPacket) : Child (state (Journal.allocate packets))
  | create (pid : PeerId) (items : List SkbId) : Child (CausalJournal.create pid items)

inductive Label where
  | staging (pid : PeerId)
  | selection (pid : PeerId)
  | take (pid : PeerId)
  | borrow (peer : Option Peer)
  | keyBorrow (kid : Option KeypairId)
  | guards (pid : PeerId) (peer : Peer) (kid : Option KeypairId)
  | nonce (pid : PeerId) (kid : KeypairId) (remaining : List Packet) (built : List DataPacket)
  | acquire (pid : PeerId)
  | rejected (pid : PeerId) (peer : Peer) (kid : Option KeypairId) (invalid : Bool)
  | restore (pid : PeerId) (packets : List Packet)
  | submit (pid : PeerId) (peer : Peer) (decision : Decision)
  | keepalive (pid : PeerId)

inductive Shape : {α : Type} → WGPrefix Event α → Type 1 where
  | pure (value : α) : Shape (pure value)
  | native (token : Native α) : Shape (liftWGPrefix token.action)
  | child (token : Child action) : Shape action
  | bind {body : WGPrefix Event α} {next : α → WGPrefix Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value)) : Shape (body >>= next)
  | receipt (record : WGRunWitness α → Event) (body : Shape action) :
      Shape (receiptWGObserved action record)
  | marked (label : Label) (body : Shape action) : Shape action

theorem lift_bind (body : WG.M α) (next : α → WG.M β) :
    (liftWGPrefix (body >>= next) : WGPrefix Event β)=
      (liftWGPrefix body >>= fun value=>liftWGPrefix (next value)) := by
  funext w a h
  change runWGPrefix (liftWGPrefix (_ >>= _)) w a h=runWGPrefix (_ >>= _) w a h
  simp only [runWGPrefix,runStatePrefix_bind,liftWGPrefix,runStatePrefix_lift,StateT.run_bind]
  cases (body.run w).run a with
  | error _=>rfl
  | ok out=>obtain ⟨⟨value,v⟩,b⟩:=out; rfl

theorem lift_pure (value : α) : (liftWGPrefix (pure value) : WGPrefix Event α)=pure value := rfl

noncomputable def listShape (xs : List α) (initial : σ)
    (body : α → σ → WGPrefix Event (ForInStep σ))
    (shapes : ∀ value acc, Shape (body value acc)) : Shape (forIn xs initial body) :=
  List.rec (motive:=fun remaining=>∀ acc,Shape (forIn remaining acc body))
    (fun acc=>.pure acc)
    (fun value rest ih acc=>(List.forIn_cons body value rest acc).symm ▸
      Shape.bind (shapes value acc) (fun decision=>match decision with
        | .done final=>.pure final
        | .yield next=>ih next)) xs initial

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging.Points
