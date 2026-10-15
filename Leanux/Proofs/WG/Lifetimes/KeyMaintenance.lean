import Leanux.Proofs.WG.Lifetimes.Session
import Leanux.Proofs.WG.Lifetimes.LookupAccess
import Leanux.Proofs.Framing.WGIndex

/-! Original key-maintenance calls with failure-retaining resident accesses.
Index removal is an inspected scalar-table action; its frame alone is not an
internal-access claim. Saved next/current keypair slots are scalar identifiers,
and their subsequent getters resolve the current store independently. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem indexRemove_identity_metadata (owner : IndexOwner) :
    SameView (fun w => (identityView w, allocationMetadata w)) (indexRemove owner) := by
  intro w x v hr
  have hf := indexRemove_sameIndexKernel owner w x v hr
  have he := congrArg (fun k => identityView {w with k}) hf
  have hm := congrArg (fun k => allocationMetadata {w with k}) hf
  apply Prod.ext
  · unfold identityView Peers.snapshot keypairResidents packetResidents at he ⊢
    simpa [indexKernelView, indexKernel, Option.bind_map, Function.comp_def] using he
  · unfold allocationMetadata deviceAllocationMetadata at hm ⊢
    simpa [indexKernelView, indexKernel, Option.map_map, Function.comp_def] using hm

theorem indexRemove_allocation (owner : IndexOwner) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (liftPrefix (indexRemove owner)) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  have hf := indexRemove_identity_metadata owner w x v hr
  exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

def resetLastSentHandshakePrefix (pid : PeerId) : MixedM Unit := do
  let now ← liftPrefix (hiddenClock64 .resetLastSent)
  let p ← getPeerMixed pid
  setPeerMixed pid {p with lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64}

def handshakeClearPrefix (pid : PeerId) : MixedM Unit := do
  _ ← peerDerefPrefix (.handshake pid)
  liftPrefix (indexRemove (.handshake pid))
  handshakeZeroPrefix pid

def invalidateSendingPrefix (kp : KeypairId) : MixedM Unit := do
  let k ← getKeypairPrefix kp
  setKeypairPrefix kp {k with sending := {k.sending with isValid := false}}

def expireCurrentPeerKeypairsPrefix (pid : PeerId) : MixedM Unit := do
  requireNotPendingMixed pid "clearing the handshake"
  _ ← peerDerefPrefix (.handshake pid)
  liftPrefix (indexRemove (.handshake pid))
  handshakeZeroPrefix pid
  resetLastSentHandshakePrefix pid
  let p ← getPeerMixed pid
  if ← liftPrefix (branch .expireNextKeypair p.keypairNext.isSome) then
    let some kp := p.keypairNext | liftPrefix (invariant "unreachable")
    invalidateSendingPrefix kp
  if ← liftPrefix (branch .expireCurrentKeypair p.keypairCurrent.isSome) then
    let some kp := p.keypairCurrent | liftPrefix (invariant "unreachable")
    invalidateSendingPrefix kp

def queuedExpiredZeroKeyMaterialPrefix (pid : PeerId) : MixedM Unit := do
  handshakeClearPrefix pid
  keypairsClearPrefix pid
  peerPutMixed (some pid)

theorem resetLastSentHandshakePrefix_erases (pid : PeerId) :
    ErasesPrefix (resetLastSentHandshakePrefix pid) (resetLastSentHandshake pid) :=
  erasesPrefix_bind (erasesPrefix_lift _) (fun _ =>
    erasesPrefix_bind (getPeerMixed_erases pid) (fun _ => setPeerMixed_erases pid _))

theorem handshakeClearPrefix_erases (pid : PeerId) :
    ErasesPrefix (handshakeClearPrefix pid) (handshakeClear pid) :=
  erasesPrefix_bind (peerDerefPrefix_erases _) (fun _ =>
    erasesPrefix_bind (erasesPrefix_lift _) (fun _ => handshakeZeroPrefix_erases pid))

theorem invalidateSendingPrefix_erases (kp : KeypairId) :
    ErasesPrefix (invalidateSendingPrefix kp)
      (do let k ← getKeypair kp; setKeypair kp {k with sending := {k.sending with isValid := false}}) :=
  erasesPrefix_bind (getKeypairPrefix_erases kp) (fun _ => setKeypairPrefix_erases kp _)

theorem expireCurrentPeerKeypairsPrefix_erases (pid : PeerId) :
    ErasesPrefix (expireCurrentPeerKeypairsPrefix pid) (expireCurrentPeerKeypairs pid) := by
  unfold expireCurrentPeerKeypairsPrefix expireCurrentPeerKeypairs handshakeClear
  simp only [bind_assoc]
  apply erasesPrefix_bind (requireNotPendingMixed_erases _ _)
  intro _
  apply erasesPrefix_bind (peerDerefPrefix_erases _)
  intro _
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro _
  apply erasesPrefix_bind (handshakeZeroPrefix_erases _)
  intro _
  apply erasesPrefix_bind (resetLastSentHandshakePrefix_erases _)
  intro _
  apply erasesPrefix_bind (getPeerMixed_erases _)
  intro p
  simp only [invalidateSendingPrefix, bind_assoc]
  cases hn : p.keypairNext <;> cases hc : p.keypairCurrent <;> simp only [hn, hc]
  all_goals
    repeat' first
      | with_reducible exact getKeypairPrefix_erases _
      | with_reducible exact setKeypairPrefix_erases _ _
      | with_reducible exact invalidateSendingPrefix_erases _
      | with_reducible exact erasesPrefix_lift _
      | with_reducible exact erasesPrefix_pure _
      | with_reducible apply erasesPrefix_bind
      | (with_reducible split)
      | (with_reducible intro x; try dsimp only)
      | rfl

theorem queuedExpiredZeroKeyMaterialPrefix_erases (pid : PeerId) :
    ErasesPrefix (queuedExpiredZeroKeyMaterialPrefix pid) (queuedExpiredZeroKeyMaterial pid) :=
  erasesPrefix_bind (handshakeClearPrefix_erases pid) (fun _ =>
    erasesPrefix_bind (keypairsClearPrefix_erases pid) (fun _ => peerPutMixed_erases _))

theorem resetLastSentHandshakePrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) : AmbientSpec I P (resetLastSentHandshakePrefix pid) (fun _ => P) := by
  unfold resetLastSentHandshakePrefix
  apply PrefixEnsures.bind (c.kernel P _ (hiddenClock64_sameKernel .resetLastSent))
  intro now
  exact PrefixEnsures.bind (c.getPeer P pid) (fun p => c.setPeer P pid
    {p with lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64})

theorem invalidateSendingPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (kp : KeypairId) : AmbientSpec I P (invalidateSendingPrefix kp) (fun _ => P) :=
  PrefixEnsures.bind (c.getKeypair P kp) (fun k =>
    c.setKeypair P kp {k with sending := {k.sending with isValid := false}})

theorem handshakeClearPrefix_preserves (c : AmbientContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (indexRemove owner)))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (handshakeClearPrefix pid) :=
  PrefixPreserves.bind (AmbientContracts.drop (peerDerefPrefix_spec c (fun _ => True) (.handshake pid))) (fun _ =>
    PrefixPreserves.bind (hi (.handshake pid)) (fun _ =>
      AmbientContracts.drop (handshakeZeroPrefix_spec_ambient c (fun _ => True) pid)))

theorem expireCurrentPeerKeypairsPrefix_preserves (c : AmbientContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (indexRemove owner)))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (expireCurrentPeerKeypairsPrefix pid) := by
  unfold expireCurrentPeerKeypairsPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (peerDerefPrefix_spec c (fun _ => True) _)
    | with_reducible exact hi _
    | with_reducible exact AmbientContracts.drop (handshakeZeroPrefix_spec_ambient c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (resetLastSentHandshakePrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (invalidateSendingPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem queuedExpiredZeroKeyMaterialPrefix_preserves (c : AmbientContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (indexRemove owner)))
    (hp : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (keypairPutPrefix kp now))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (queuedExpiredZeroKeyMaterialPrefix pid) :=
  PrefixPreserves.bind (handshakeClearPrefix_preserves c hi pid) (fun _ =>
    PrefixPreserves.bind (keypairsClearPrefix_preserves_ambient c hp pid) (fun _ => c.peerPut _))

inductive KeyMaintenanceCall where
  | reset (pid : PeerId)
  | clear (pid : PeerId)
  | expire (pid : PeerId)
  | queuedClear (pid : PeerId)

namespace KeyMaintenanceCall

def original : KeyMaintenanceCall → M Unit
  | .reset pid => resetLastSentHandshake pid
  | .clear pid => handshakeClear pid
  | .expire pid => expireCurrentPeerKeypairs pid
  | .queuedClear pid => queuedExpiredZeroKeyMaterial pid

def observed : KeyMaintenanceCall → MixedM Unit
  | .reset pid => resetLastSentHandshakePrefix pid
  | .clear pid => handshakeClearPrefix pid
  | .expire pid => expireCurrentPeerKeypairsPrefix pid
  | .queuedClear pid => queuedExpiredZeroKeyMaterialPrefix pid

theorem erases (call : KeyMaintenanceCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | reset pid => exact resetLastSentHandshakePrefix_erases pid
  | clear pid => exact handshakeClearPrefix_erases pid
  | expire pid => exact expireCurrentPeerKeypairsPrefix_erases pid
  | queuedClear pid => exact queuedExpiredZeroKeyMaterialPrefix_erases pid

theorem preserves_ambient (c : AmbientContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (indexRemove owner)))
    (hp : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (keypairPutPrefix kp now))
    (call : KeyMaintenanceCall) : PrefixPreserves I LifetimeEvent.Safe call.observed := by
  cases call with
  | reset pid => exact AmbientContracts.drop (resetLastSentHandshakePrefix_spec c (fun _ => True) pid)
  | clear pid => exact handshakeClearPrefix_preserves c hi pid
  | expire pid => exact expireCurrentPeerKeypairsPrefix_preserves c hi pid
  | queuedClear pid => exact queuedExpiredZeroKeyMaterialPrefix_preserves c hi hp pid

theorem allocation (call : KeyMaintenanceCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient indexRemove_allocation keypairPutPrefix_allocation

end KeyMaintenanceCall
end Leanux.Proofs.WG.Lifetimes
