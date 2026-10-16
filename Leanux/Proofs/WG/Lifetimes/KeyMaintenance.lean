import Leanux.Proofs.WG.Lifetimes.Session
import Leanux.Proofs.WG.Lifetimes.LookupAccess
import Leanux.Proofs.Framing.WGIndex

/-! Original key-maintenance calls with failure-retaining resident accesses.
Index removal is an inspected scalar-table action; its frame alone is not an
internal-access claim. Saved next/current keypair slots are scalar identifiers,
and their subsequent getters resolve the current store independently. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem indexRemove_allocation (owner : IndexOwner) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe
      (liftWGPrefix (liftIndex (indexRemove owner))) := by
  apply StatePrefixEnsures.lift _ (fun h w _ hi => hi.safe)
  intro h w ambient x v ambient' hi hr
  have hp : Hoare (liftIndex (indexRemove owner)) (AllocationInv h)
      (fun _ => AllocationInv h) := by
    apply hoare_liftIndex
    intro g d table hg hd
    apply hg.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [hd]
    · simp [allocationMetadata, deviceAllocationMetadata, hd]
  exact (hoare_iff_run_ambient _ _ _).mp hp w ambient x v ambient' hi hr

def resetLastSentHandshakePrefix (pid : PeerId) : MixedM Unit := do
  let now ← liftWGPrefix (hiddenClock64 .resetLastSent)
  let p ← getPeerMixed pid
  setPeerMixed pid {p with lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64}

def handshakeClearPrefix (pid : PeerId) : MixedM Unit := do
  _ ← peerDerefPrefix (.handshake pid)
  liftWGPrefix (liftIndex (indexRemove (.handshake pid)))
  handshakeZeroPrefix pid

def invalidateSendingPrefix (kp : KeypairId) : MixedM Unit := do
  let k ← getKeypairPrefix kp
  setKeypairPrefix kp {k with sending := {k.sending with isValid := false}}

def expireCurrentPeerKeypairsPrefix (pid : PeerId) : MixedM Unit := do
  requireNotPendingMixed pid "clearing the handshake"
  _ ← peerDerefPrefix (.handshake pid)
  liftWGPrefix (liftIndex (indexRemove (.handshake pid)))
  handshakeZeroPrefix pid
  resetLastSentHandshakePrefix pid
  let p ← getPeerMixed pid
  if ← liftWGPrefix (branch .expireNextKeypair p.keypairNext.isSome) then
    let some kp := p.keypairNext | liftWGPrefix (invariant "unreachable")
    invalidateSendingPrefix kp
  if ← liftWGPrefix (branch .expireCurrentKeypair p.keypairCurrent.isSome) then
    let some kp := p.keypairCurrent | liftWGPrefix (invariant "unreachable")
    invalidateSendingPrefix kp

def queuedExpiredZeroKeyMaterialPrefix (pid : PeerId) : MixedM Unit := do
  handshakeClearPrefix pid
  keypairsClearPrefix pid
  peerPutMixed (some pid)

theorem resetLastSentHandshakePrefix_erases (pid : PeerId) :
    ErasesStatePrefix (resetLastSentHandshakePrefix pid) (resetLastSentHandshake pid) :=
  erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
    erasesStatePrefix_bind (getPeerMixed_erases pid) (fun _ => setPeerMixed_erases pid _))

theorem handshakeClearPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (handshakeClearPrefix pid) (handshakeClear pid) :=
  erasesStatePrefix_bind (peerDerefPrefix_erases _) (fun _ =>
    erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => handshakeZeroPrefix_erases pid))

theorem invalidateSendingPrefix_erases (kp : KeypairId) :
    ErasesStatePrefix (invalidateSendingPrefix kp)
      (do let k ← getKeypair kp; setKeypair kp {k with sending := {k.sending with isValid := false}}) :=
  erasesStatePrefix_bind (getKeypairPrefix_erases kp) (fun _ => setKeypairPrefix_erases kp _)

theorem expireCurrentPeerKeypairsPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (expireCurrentPeerKeypairsPrefix pid) (expireCurrentPeerKeypairs pid) := by
  unfold expireCurrentPeerKeypairsPrefix expireCurrentPeerKeypairs handshakeClear
  simp only [bind_assoc]
  apply erasesStatePrefix_bind (requireNotPendingMixed_erases _ _)
  intro _
  apply erasesStatePrefix_bind (peerDerefPrefix_erases _)
  intro _
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro _
  apply erasesStatePrefix_bind (handshakeZeroPrefix_erases _)
  intro _
  apply erasesStatePrefix_bind (resetLastSentHandshakePrefix_erases _)
  intro _
  apply erasesStatePrefix_bind (getPeerMixed_erases _)
  intro p
  simp only [invalidateSendingPrefix, bind_assoc]
  cases hn : p.keypairNext <;> cases hc : p.keypairCurrent <;> simp only [hn, hc]
  all_goals
    repeat' first
      | with_reducible exact getKeypairPrefix_erases _
      | with_reducible exact setKeypairPrefix_erases _ _
      | with_reducible exact invalidateSendingPrefix_erases _
      | exact erasesStatePrefix_lift _
      | with_reducible exact erasesStatePrefix_pure _
      | with_reducible apply erasesStatePrefix_bind
      | (with_reducible split)
      | (with_reducible intro x; try dsimp only)
      | rfl

theorem queuedExpiredZeroKeyMaterialPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (queuedExpiredZeroKeyMaterialPrefix pid) (queuedExpiredZeroKeyMaterial pid) :=
  erasesStatePrefix_bind (handshakeClearPrefix_erases pid) (fun _ =>
    erasesStatePrefix_bind (keypairsClearPrefix_erases pid) (fun _ => peerPutMixed_erases _))

theorem resetLastSentHandshakePrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) : AmbientSpec I P (resetLastSentHandshakePrefix pid) (fun _ => P) := by
  unfold resetLastSentHandshakePrefix
  apply StatePrefixEnsures.bind (c.store P _ (fun initial =>
    hoare_liftAmbient (AmbientM.hiddenClock64 .resetLastSent) (fun w => wgStoreView w = initial)))
  intro now
  exact StatePrefixEnsures.bind (c.getPeer P pid) (fun p => c.setPeer P pid
    {p with lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64})

theorem invalidateSendingPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (kp : KeypairId) : AmbientSpec I P (invalidateSendingPrefix kp) (fun _ => P) :=
  StatePrefixEnsures.bind (c.getKeypair P kp) (fun k =>
    c.setKeypair P kp {k with sending := {k.sending with isValid := false}})

theorem handshakeClearPrefix_preserves (c : AmbientContracts I)
    (hi : ∀ owner, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (liftIndex (indexRemove owner))))
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (handshakeClearPrefix pid) :=
  StatePrefixEnsures.bind (AmbientContracts.drop (peerDerefPrefix_spec c (fun _ => True) (.handshake pid))) (fun _ =>
    StatePrefixEnsures.bind (hi (.handshake pid)) (fun _ =>
      AmbientContracts.drop (handshakeZeroPrefix_spec_ambient c (fun _ => True) pid)))

theorem expireCurrentPeerKeypairsPrefix_preserves (c : AmbientContracts I)
    (hi : ∀ owner, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (liftIndex (indexRemove owner))))
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (expireCurrentPeerKeypairsPrefix pid) := by
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
    | with_reducible exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
    | with_reducible apply StatePrefixEnsures.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem queuedExpiredZeroKeyMaterialPrefix_preserves (c : AmbientContracts I)
    (hi : ∀ owner, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (liftIndex (indexRemove owner))))
    (hp : ∀ kp now, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keypairPutPrefix kp now))
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (queuedExpiredZeroKeyMaterialPrefix pid) :=
  StatePrefixEnsures.bind (handshakeClearPrefix_preserves c hi pid) (fun _ =>
    StatePrefixEnsures.bind (keypairsClearPrefix_preserves_ambient c hp pid) (fun _ => c.peerPut _))


/-- Product callers retain arbitrary history invariants over the full World. -/
theorem resetLastSentHandshakePrefix_spec_product (c : ProductAmbientContracts I)
    (P : IdentityView → Prop) (pid : PeerId) :
    ProductAmbientSpec I P (liftWGObserver (resetLastSentHandshakePrefix pid)) (fun _ => P) := by
  simp only [resetLastSentHandshakePrefix, liftWGObserver_bind]
  apply PrefixEnsures.bind (c.nativeStore P _ (fun initial =>
    hoare_liftAmbient (AmbientM.hiddenClock64 .resetLastSent) (fun w => wgStoreView w = initial)))
  intro now
  exact PrefixEnsures.bind (c.getPeer P pid) (fun p => c.setPeer P pid
    {p with lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64})

theorem invalidateSendingPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (kp : KeypairId) :
    ProductAmbientSpec I P (liftWGObserver (invalidateSendingPrefix kp)) (fun _ => P) := by
  simp only [invalidateSendingPrefix, liftWGObserver_bind]
  exact PrefixEnsures.bind (c.getKeypair P kp) (fun k =>
    c.setKeypair P kp {k with sending := {k.sending with isValid := false}})

theorem handshakeClearPrefix_preserves_product (c : ProductAmbientContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (liftIndex (indexRemove owner)))))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (handshakeClearPrefix pid)) := by
  simp only [handshakeClearPrefix, liftWGObserver_bind]
  exact PrefixPreserves.bind (ProductAmbientContracts.drop (c.peerDeref (fun _ => True) (.handshake pid))) (fun _ =>
    PrefixPreserves.bind (hi (.handshake pid)) (fun _ =>
      ProductAmbientContracts.drop (handshakeZeroPrefix_spec_product c (fun _ => True) pid)))

theorem expireCurrentPeerKeypairsPrefix_preserves_product (c : ProductAmbientContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (liftIndex (indexRemove owner)))))
    (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (expireCurrentPeerKeypairsPrefix pid)) := by
  have ambient_spec {α : Type} (a : AmbientM α) :
      ProductAmbientSpec I (fun _ => True)
        (liftWGObserver (liftWGPrefix (MonadLift.monadLift a : WG.M α))) (fun _ _ => True) :=
    c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient a (fun w => wgStoreView w = initial))
  simp only [expireCurrentPeerKeypairsPrefix, liftWGObserver_bind]
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (requireNotPendingMixed_spec_product c (fun _ => True) pid _))
  intro _
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.peerDeref (fun _ => True) (.handshake pid)))
  intro _
  apply PrefixPreserves.bind (hi (.handshake pid))
  intro _
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (handshakeZeroPrefix_spec_product c (fun _ => True) pid))
  intro _
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (resetLastSentHandshakePrefix_spec_product c (fun _ => True) pid))
  intro _
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) pid))
  intro p
  have last : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (do
        if ← liftWGPrefix (branch .expireCurrentKeypair p.keypairCurrent.isSome) then
          let some kp := p.keypairCurrent | liftWGPrefix (invariant "unreachable")
          invalidateSendingPrefix kp)) := by
    simp only [liftWGObserver_bind]
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (ambient_spec (AmbientM.branch _ _)))
    intro yes
    split
    · cases p.keypairCurrent with
      | none => exact ProductAmbientContracts.drop (ambient_spec (AmbientM.invariant _))
      | some kp => exact ProductAmbientContracts.drop (invalidateSendingPrefix_spec_product c (fun _ => True) kp)
    · simpa only [liftWGObserver_pure] using PrefixPreserves.pure c.safe ()
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (ambient_spec (AmbientM.branch _ _)))
  intro yes
  split
  · cases p.keypairNext with
    | none => exact ProductAmbientContracts.drop (ambient_spec (AmbientM.invariant _))
    | some kp =>
      simp only [liftWGObserver_bind]
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (invalidateSendingPrefix_spec_product c (fun _ => True) kp))
      intro _
      exact last
  · exact last

theorem queuedExpiredZeroKeyMaterialPrefix_preserves_product (c : ProductAmbientContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (liftIndex (indexRemove owner)))))
    (hp : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairPutPrefix kp now)))
    (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (queuedExpiredZeroKeyMaterialPrefix pid)) := by
  simp only [queuedExpiredZeroKeyMaterialPrefix, liftWGObserver_bind]
  exact PrefixPreserves.bind (handshakeClearPrefix_preserves_product c hi pid) (fun _ =>
    PrefixPreserves.bind (keypairsClearPrefix_preserves_product c hp pid) (fun _ => c.peerPut _))

inductive KeyMaintenanceCall where
  | reset (pid : PeerId)
  | clear (pid : PeerId)
  | expire (pid : PeerId)
  | queuedClear (pid : PeerId)

namespace KeyMaintenanceCall

def original : KeyMaintenanceCall → WG.M Unit
  | .reset pid => resetLastSentHandshake pid
  | .clear pid => handshakeClear pid
  | .expire pid => expireCurrentPeerKeypairs pid
  | .queuedClear pid => queuedExpiredZeroKeyMaterial pid

def observed : KeyMaintenanceCall → MixedM Unit
  | .reset pid => resetLastSentHandshakePrefix pid
  | .clear pid => handshakeClearPrefix pid
  | .expire pid => expireCurrentPeerKeypairsPrefix pid
  | .queuedClear pid => queuedExpiredZeroKeyMaterialPrefix pid

theorem erases (call : KeyMaintenanceCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | reset pid => exact resetLastSentHandshakePrefix_erases pid
  | clear pid => exact handshakeClearPrefix_erases pid
  | expire pid => exact expireCurrentPeerKeypairsPrefix_erases pid
  | queuedClear pid => exact queuedExpiredZeroKeyMaterialPrefix_erases pid

theorem preserves_ambient (c : AmbientContracts I)
    (hi : ∀ owner, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (liftIndex (indexRemove owner))))
    (hp : ∀ kp now, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keypairPutPrefix kp now))
    (call : KeyMaintenanceCall) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call with
  | reset pid => exact AmbientContracts.drop (resetLastSentHandshakePrefix_spec c (fun _ => True) pid)
  | clear pid => exact handshakeClearPrefix_preserves c hi pid
  | expire pid => exact expireCurrentPeerKeypairsPrefix_preserves c hi pid
  | queuedClear pid => exact queuedExpiredZeroKeyMaterialPrefix_preserves c hi hp pid

theorem preserves_product (c : ProductAmbientContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (liftIndex (indexRemove owner)))))
    (hp : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairPutPrefix kp now)))
    (call : KeyMaintenanceCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  cases call with
  | reset pid => exact ProductAmbientContracts.drop (resetLastSentHandshakePrefix_spec_product c (fun _ => True) pid)
  | clear pid => exact handshakeClearPrefix_preserves_product c hi pid
  | expire pid => exact expireCurrentPeerKeypairsPrefix_preserves_product c hi pid
  | queuedClear pid => exact queuedExpiredZeroKeyMaterialPrefix_preserves_product c hi hp pid

theorem allocation (call : KeyMaintenanceCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient indexRemove_allocation keypairPutPrefix_allocation

end KeyMaintenanceCall
end Leanux.Proofs.WG.Lifetimes
