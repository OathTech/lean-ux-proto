import Leanux.Proofs.WG.HandshakeSecurity.ReservationSelectionSource
import Leanux.Proofs.WG.RetirementSecurity.Frames

/-! Exact source cuts in the nonce-limit rejection arm. Invalidation precedes
the key put; the entire detached batch is restored before the guarded handshake
request, whose hidden clock may Stop. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.NonceRejection
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

def invalidate (kid : KeypairId) : WG.M Unit := do
  let key ← getKeypair kid
  setKeypair kid {key with sending := {key.sending with isValid := false}}

def restore (pid : PeerId) (packets : List Packet) : WG.M Unit := do
  setPeer pid {(← getPeer pid) with staged := packets ++ (← getPeer pid).staged}

def release (kid : KeypairId) (packets : List Packet) : WG.M Unit := do
  keypairPut (some kid) false
  for _ in packets do _ ← branch .stagedOrphanWalk true
  _ ← branch .stagedOrphanWalk false

theorem factor (pid : PeerId) (packets : List Packet) (kid : KeypairId) :
    stagedOutNokey pid packets (some kid) true = (do
      invalidate kid
      release kid packets
      restore pid packets
      sendQueuedHandshakeInitiation pid false) := by
  simp only [stagedOutNokey,invalidate,release,restore,bind_assoc,pure_bind,↓reduceIte]

inductive Event where
  | invalidated (kid : KeypairId) (run : WGRunWitness Unit)
  | restored (pid : PeerId) (packets : List Packet) (run : WGRunWitness Unit)

def Event.Valid : Event → Prop
  | .invalidated kid r => r.Valid (invalidate kid)
  | .restored pid packets r => r.Valid (restore pid packets)

def observe (pid : PeerId) (packets : List Packet) (kid : KeypairId) : WGPrefix Event Unit := do
  receiptWGObserved (liftWGPrefix (invalidate kid)) (.invalidated kid)
  liftWGPrefix (release kid packets)
  receiptWGObserved (liftWGPrefix (restore pid packets)) (.restored pid packets)
  liftWGPrefix (sendQueuedHandshakeInitiation pid false)

theorem erases (pid : PeerId) (packets : List Packet) (kid : KeypairId) :
    ErasesStatePrefix (observe pid packets kid) (stagedOutNokey pid packets (some kid) true) := by
  rw [factor]
  unfold observe
  apply erasesStatePrefix_bind (receiptWGObserved_erases (erasesStatePrefix_lift _) _)
  intro _
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro _
  apply erasesStatePrefix_bind (receiptWGObserved_erases (erasesStatePrefix_lift _) _)
  intro _
  exact erasesStatePrefix_lift _

/-- The native true counter branch takes this exact invalidation/restoration
arm, with its original comparison record and no queue-admission suffix. -/
theorem branch_rejected (pid : PeerId) (packets : List Packet) (kid nonce : Nat)
    (limit : REJECT_AFTER_MESSAGES ≤ nonce) (w : WGWorld) (a : Ambient) :
    ((do
      if ← branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES then
        stagedOutNokey pid packets (some kid) true).run w).run a =
      ((stagedOutNokey pid packets (some kid) true).run w).run
        (CounterWindow.recordCmp a .stagedNonceRejected true nonce REJECT_AFTER_MESSAGES) := by
  simp only [branchCmp,StateT.run_bind,limit,decide_true]
  rfl

end Leanux.Proofs.WG.HandshakeSecurity.NonceRejection
