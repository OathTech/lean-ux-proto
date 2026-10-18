import Leanux.Proofs.WG.RetirementSecurity.HolderFrames
import Leanux.Proofs.WG.Keypairs.Frames.WGTransitions
import Leanux.Proofs.WG.Origins.RetainingLifecycle

/-! Scalar frames keep allocation identity, sending nonce and key-reference
count while native session derivation or expiry changes key material/validity.
These are projections of the original actions, not modified mirror setters. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes

def referenceNonceFields (k : Keypair) : Nat × Nat × Nat :=
  (k.internalId,k.sendingCounter,k.refcount)

def referenceNonceView (w : WGWorld) : Nat × (KeypairId → Option (Nat × Nat × Nat)) :=
  (w.keypairCounter,fun id => (keyAt w id).map referenceNonceFields)

theorem full_keys_frontier_frame (action : WG.M α)
    (keys : SameView Origins.view action) (frontier : Keypairs.SameSnapshot action) :
    SameView referenceNonceView action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have hk := (ProjectedAction.iff_run_ambient _ _ _).mp keys w a result v b run
  have hf := (ProjectedAction.iff_run_ambient _ _ _).mp frontier w a result v b run
  apply Prod.ext
  · exact congrArg Keypairs.Snapshot.frontier hf
  · funext id
    have same := congrArg (fun view => view.bind fun fields => fields.2 id) hk
    have sameKey : keyAt v id = keyAt w id := by
      simpa only [Origins.view,keyAt,Option.bind_map,Function.comp_def] using same
    exact congrArg (Option.map referenceNonceFields) sameKey

theorem ambient_referenceNonce (action : AmbientM α) :
    SameView referenceNonceView (monadLift action : WG.M α) :=
  fun initial => hoare_liftAmbient action (fun w => referenceNonceView w = initial)

theorem update_key_referenceNonce (id : KeypairId) (f : Keypair → Keypair)
    (fields : ∀ k, referenceNonceFields (f k) = referenceNonceFields k) :
    SameView referenceNonceView (do let k ← getKeypair id; setKeypair id (f k)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨k,u,c,read,write⟩ := run
  obtain ⟨worldSame,ambientSame,d,device,resident⟩ := KeyTimes.getKeypair_return id w u k a c read
  subst u
  subst c
  rw [CounterWindow.setKeypair_run] at write
  cases write
  apply Prod.ext
  · rfl
  · funext other
    by_cases same : id = other
    · subst other
      simp [referenceNonceView,CounterWindow.store,keyAt,device,resident,fields]
    · simp [referenceNonceView,CounterWindow.store,keyAt,device,
        Std.TreeMap.getElem?_insert,same]

theorem deriveKeys_referenceNonce (id : KeypairId) (initiator : Bool) (ck : List UInt8) :
    SameView referenceNonceView (deriveKeys id initiator ck) := by
  unfold deriveKeys
  apply SameView.bind (ambient_referenceNonce (AmbientM.hiddenClock64 .deriveKeysBirthdate))
  intro born
  apply SameView.bind ((kdf_sameWGWorld true false ck []).factor referenceNonceView)
  intro outputs
  apply SameView.bind ((kdfOut_sameWGWorld outputs 0).factor referenceNonceView)
  intro first
  apply SameView.bind ((kdfOut_sameWGWorld outputs 1).factor referenceNonceView)
  intro second
  apply update_key_referenceNonce
  intro k
  cases initiator <;> rfl

theorem initKey_referenceNonce (id : KeypairId) (initiator : Bool) (remote : Nat) :
    SameView referenceNonceView (SessionOrigin.initKey id initiator remote) :=
  update_key_referenceNonce id (fun k => {k with iAmTheInitiator := initiator, remoteIndex := remote})
    (fun _ => rfl)

theorem handshakeClear_referenceNonce (pid : PeerId) :
    SameView referenceNonceView (handshakeClear pid) :=
  full_keys_frontier_frame _ (Origins.Retaining.handshakeClear_material pid)
    (Keypairs.WGTransitions.handshakeClear_sameSnapshot pid)

theorem resetLastSent_referenceNonce (pid : PeerId) :
    SameView referenceNonceView (resetLastSentHandshake pid) :=
  full_keys_frontier_frame _ (Origins.Retaining.resetLastSentHandshake_material pid)
    (Keypairs.WGFrames.resetLastSentHandshake_sameSnapshot pid)

theorem getPeer_referenceNonce (pid : PeerId) : SameView referenceNonceView (getPeer pid) :=
  full_keys_frontier_frame _ (Origins.getPeer_view pid) (Keypairs.WGFrames.getPeer_sameSnapshot pid)

theorem expire_referenceNonce (pid : PeerId) :
    SameView referenceNonceView (expireCurrentPeerKeypairs pid) := by
  have invalidate (id : KeypairId) : SameView referenceNonceView
      (do let k ← getKeypair id; setKeypair id {k with sending := {k.sending with isValid := false}}) :=
    update_key_referenceNonce id _ (fun _ => rfl)
  unfold expireCurrentPeerKeypairs requireNotPending
  apply SameView.bind (SameView.pure referenceNonceView ())
  intro _
  apply SameView.bind (handshakeClear_referenceNonce pid)
  intro _
  apply SameView.bind (resetLastSent_referenceNonce pid)
  intro _
  apply SameView.bind (getPeer_referenceNonce pid)
  intro p
  have one (decision : Decision) (kp : Option KeypairId) : SameView referenceNonceView
      (do if ← branch decision kp.isSome then
            let some id := kp | invariant "unreachable"
            let k ← getKeypair id
            setKeypair id {k with sending := {k.sending with isValid := false}}) := by
    apply SameView.bind (ambient_referenceNonce (AmbientM.branch decision kp.isSome))
    intro selected
    cases selected with
    | false => exact SameView.pure referenceNonceView ()
    | true =>
      cases kp with
      | none => exact ambient_referenceNonce (AmbientM.invariant "unreachable")
      | some id => exact invalidate id
  have current := one .expireCurrentKeypair p.keypairCurrent
  apply SameView.bind (ambient_referenceNonce (AmbientM.branch .expireNextKeypair p.keypairNext.isSome))
  intro selected
  cases selected with
  | false => exact current
  | true =>
    cases lookup : p.keypairNext with
    | none => exact SameView.bind (ambient_referenceNonce (AmbientM.invariant "unreachable")) (fun _ => current)
    | some id => exact SameView.bind (invalidate id) (fun _ => current)

theorem Credits.Exact.referenceNonce (account : Credits.Exact credits w)
    (same : referenceNonceView v = referenceNonceView w) : Credits.Exact credits v := by
  intro allocation
  have cells := congrFun (congrArg Prod.snd same) allocation.slot
  change (keyAt v allocation.slot).map referenceNonceFields =
    (keyAt w allocation.slot).map referenceNonceFields at cells
  cases before : keyAt w allocation.slot with
  | none =>
    cases after : keyAt v allocation.slot with
    | none => simpa only [Credits.balance,before,after] using account allocation
    | some k => simp [before,after] at cells
  | some old =>
    cases after : keyAt v allocation.slot with
    | none => simp [before,after] at cells
    | some k =>
      have fields : referenceNonceFields k = referenceNonceFields old := by
        simpa only [before,after,Option.map_some,Option.some.injEq] using cells
      have stamp : k.internalId = old.internalId := congrArg Prod.fst fields
      have refs : k.refcount = old.refcount := congrArg (fun f : Nat × Nat × Nat => f.2.2) fields
      have sameBalance : Credits.balance v allocation = Credits.balance w allocation := by
        simp [Credits.balance,before,after,stamp,refs]
      exact (account allocation).trans sameBalance.symm

theorem referenceNonce_projection (same : referenceNonceView v = referenceNonceView w) :
    v.keypairCounter = w.keypairCounter ∧
      ∀ id k, keyAt v id = some k → ∃ old, keyAt w id = some old ∧
        k.internalId = old.internalId ∧ k.sendingCounter = old.sendingCounter := by
  refine ⟨congrArg Prod.fst same,?_⟩
  intro id k found
  have cells := congrFun (congrArg Prod.snd same) id
  change (keyAt v id).map referenceNonceFields = (keyAt w id).map referenceNonceFields at cells
  rw [found] at cells
  cases old : keyAt w id with
  | none => simp [old] at cells
  | some before =>
    have fields : referenceNonceFields k = referenceNonceFields before := by simpa [old] using cells
    exact ⟨before,rfl,congrArg Prod.fst fields,congrArg (fun f : Nat × Nat × Nat => f.2.1) fields⟩

theorem derive_nonce_projection (id : KeypairId) (initiator : Bool) (ck : List UInt8)
    (w v : WGWorld) (a b : Ambient)
    (run : ((deriveKeys id initiator ck).run w).run a = .ok (((),v),b)) :
    v.keypairCounter = w.keypairCounter ∧
      ∀ slot k, keyAt v slot = some k → ∃ old, keyAt w slot = some old ∧
        k.internalId = old.internalId ∧ k.sendingCounter = old.sendingCounter :=
  referenceNonce_projection ((ProjectedAction.iff_run_ambient _ _ _).mp
    (deriveKeys_referenceNonce id initiator ck) w a () v b run)

theorem init_nonce_projection (id : KeypairId) (initiator : Bool) (remote : Nat)
    (w v : WGWorld) (a b : Ambient)
    (run : ((SessionOrigin.initKey id initiator remote).run w).run a = .ok (((),v),b)) :
    v.keypairCounter = w.keypairCounter ∧
      ∀ slot k, keyAt v slot = some k → ∃ old, keyAt w slot = some old ∧
        k.internalId = old.internalId ∧ k.sendingCounter = old.sendingCounter :=
  referenceNonce_projection ((ProjectedAction.iff_run_ambient _ _ _).mp
    (initKey_referenceNonce id initiator remote) w a () v b run)

theorem expire_nonce_projection (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((expireCurrentPeerKeypairs pid).run w).run a = .ok (((),v),b)) :
    v.keypairCounter = w.keypairCounter ∧
      ∀ slot k, keyAt v slot = some k → ∃ old, keyAt w slot = some old ∧
        k.internalId = old.internalId ∧ k.sendingCounter = old.sendingCounter :=
  referenceNonce_projection ((ProjectedAction.iff_run_ambient _ _ _).mp
    (expire_referenceNonce pid) w a () v b run)

theorem Credits.referenceNonce_preserves (action : WG.M α)
    (frame : SameView referenceNonceView action) (credits : Credits.Ledger) :
    Preserves (Credits.Exact credits) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact hi.referenceNonce ((ProjectedAction.iff_run_ambient _ _ _).mp frame w a result v b run)

theorem deriveKeys_peers (id : KeypairId) (initiator : Bool) (ck : List UInt8) :
    SameView peersAt (deriveKeys id initiator ck) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  obtain ⟨d,old,key,device,_,after,_,_,_⟩ := Origins.derive_effect id initiator ck w v a b run
  simp only [peersAt,device,after,Option.map_some]

theorem initKey_peers (id : KeypairId) (initiator : Bool) (remote : Nat) :
    SameView peersAt (SessionOrigin.initKey id initiator remote) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  obtain ⟨d,k,device,_,after⟩ := Origins.initKey_effect id initiator remote w v a b run
  simp only [peersAt,device,after,Option.map_some]

end Leanux.Proofs.WG.RetirementSecurity
