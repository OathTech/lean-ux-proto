import Leanux.Proofs.WG.Keypairs.SessionOrigin

/-! Observe the real session allocation callback before later derivation,
handshake zeroing, rotation or publication can Stop. The campaign-1 source
factor is reused unchanged. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Installation
open Leanux Leanux.WG Leanux.Proofs.Logged

structure AllocationReceipt where
  word : Option PeerId
  execution : WGRunWitness (Option KeypairId)

def AllocationReceipt.Valid (r : AllocationReceipt) : Prop :=
  r.execution.Valid (keypairCreate r.word)

def createObserved (word : Option PeerId) : WGPrefix AllocationReceipt (Option KeypairId) :=
  receiptWGObserved (liftWGPrefix (keypairCreate word)) (fun r => ⟨word, r⟩)

def frontObserved (pid : PeerId) : WGPrefix AllocationReceipt (Option SessionOrigin.Context) :=
  SessionOrigin.frontWith (fun p => liftWGPrefix (getPeer p))
    (fun word => liftWGPrefix (IndexOwner.peerWord word)) createObserved
    (fun k b i => liftWGPrefix (SessionOrigin.initKey k b i))
    (fun k b ck => liftWGPrefix (deriveKeys k b ck)) liftWGPrefix pid

def observed (pid : PeerId) : WGPrefix AllocationReceipt Bool := do
  match ← frontObserved pid with
  | none => pure false
  | some context => liftWGPrefix (SessionOrigin.tail pid context.slot)

theorem create_erases (word : Option PeerId) :
    ErasesStatePrefix (createObserved word) (keypairCreate word) :=
  receiptWGObserved_erases (erasesStatePrefix_lift _) _

theorem front_erases (pid : PeerId) :
    ErasesStatePrefix (frontObserved pid) (SessionOrigin.front pid) := by
  have lifted {α : Type} (a : WG.M α) :
      ErasesStatePrefix (liftWGPrefix a : WGPrefix AllocationReceipt α) a :=
    erasesStatePrefix_lift a
  unfold frontObserved SessionOrigin.front SessionOrigin.frontWith
  repeat' first
    | with_reducible exact create_erases _
    | with_reducible exact lifted _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem erases (pid : PeerId) : ErasesStatePrefix (observed pid) (beginSession pid) := by
  rw [SessionOrigin.factor]
  unfold observed
  apply erasesStatePrefix_bind (front_erases pid)
  intro result
  cases result with
  | none => exact erasesStatePrefix_pure _
  | some context => exact erasesStatePrefix_lift _

end Leanux.Proofs.WG.HandshakeSecurity.Installation
