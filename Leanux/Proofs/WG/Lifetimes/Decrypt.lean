import Leanux.Proofs.WG.Lifetimes.Enqueue

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Decryption observations. Only the original access-free rejection expression
is factored; both keypair reads and the validity update remain explicit. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def decryptKeyReject (k : Keypair) : WG.M Bool :=
  WG.orM (branch .decKeyInvalid !k.receiving.isValid) do
    WG.orM (branchExpired .decKeyExpired k.receiving.birthdate REJECT_AFTER_TIME)
      (branchCmp .decCounterLimit (k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES)
        k.receivingCounter.counter REJECT_AFTER_MESSAGES)

theorem orM_sameView {S V : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {view : S → V} {a b : StateT S m Bool}
    (ha : SameView view a) (hb : SameView view b) :
    SameView view (do if ← a then pure true else b) := by
  apply SameView.bind ha
  intro yes
  split
  · exact SameView.pure view true
  · exact hb

theorem decryptKeyReject_sameWGStore (k : Keypair) : SameWGStore (decryptKeyReject k) := by
  unfold decryptKeyReject
  apply orM_sameView
  · intro initial
    exact hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial)
  · apply orM_sameView
    · exact (branchExpired_sameWGWorld _ _ _).of_factor wgStoreView wgStoreView (fun _ => rfl)
    · intro initial
      exact hoare_liftAmbient (AmbientM.branchCmp _ _ _ _) (fun w => wgStoreView w = initial)

def decryptPacketPrefix (pkt : RxPacket) : MixedM (Option RxPacket) := do
  if ← liftWGPrefix (branch .decNoKeypair false) then return none
  let k ← getKeypairPrefix pkt.keypair
  let reject ← liftWGPrefix (decryptKeyReject k)
  if reject then
    let k ← getKeypairPrefix pkt.keypair
    setKeypairPrefix pkt.keypair { k with receiving := { k.receiving with isValid := false } }
    return none
  let nonce := u64le pkt.bytes 8
  let cowOk ← liftWGPrefix (hiddenAlloc .skbCowDataRx)
  if ← liftWGPrefix (WG.orM (branch .decCowDataFailed !cowOk) (branch .decTooManyFrags false)) then return none
  if ← liftWGPrefix (branch .decSgvecFailed false) then return none
  let plain := aeadDecrypt k.receiving.key (counterNonce nonce) (pkt.bytes.drop 16) []
  if ← liftWGPrefix (branch .decDecryptFailed plain.isNone) then return none
  let some bytes := plain | liftWGPrefix (invariant "unreachable")
  if ← liftWGPrefix (branch .decTrimFailed false) then return none
  return some { pkt with nonce, bytes }

theorem decryptPacketPrefix_erases (pkt : RxPacket) :
    ErasesStatePrefix (decryptPacketPrefix pkt) (decryptPacket pkt) := by
  unfold decryptPacketPrefix decryptPacket decryptKeyReject
  repeat' first
    | rfl
    | exact getKeypairPrefix_erases _
    | exact setKeypairPrefix_erases _ _
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | apply erasesStatePrefix_bind
    | intro x
    | split
  all_goals simp_all [runStatePrefix_pure, runStatePrefix_lift]

theorem decryptPacketPrefix_spec_ambient (c : AmbientContracts I) (P : IdentityView → Prop) (pkt : RxPacket) :
    AmbientSpec I P (decryptPacketPrefix pkt) (fun _ => P) := by
  unfold decryptPacketPrefix
  apply StatePrefixEnsures.bind (c.branch P _ _)
  intro noKey
  split
  · exact c.pure P none
  · apply StatePrefixEnsures.bind (c.getKeypair_frame P pkt.keypair)
    intro k
    apply StatePrefixEnsures.bind (c.store P _ (decryptKeyReject_sameWGStore k))
    intro reject
    split
    · apply StatePrefixEnsures.bind (c.getKeypair P pkt.keypair)
      intro fresh
      apply StatePrefixEnsures.bind (c.setKeypair P pkt.keypair
        {fresh with receiving := {fresh.receiving with isValid := false}})
      intro _
      exact c.pure P none
    · apply StatePrefixEnsures.bind (c.store P _ (by intro initial; exact hoare_liftAmbient (AmbientM.hiddenAlloc .skbCowDataRx) (fun w => wgStoreView w = initial)))
      intro cowOk
      apply StatePrefixEnsures.bind (c.store P _
        (orM_sameView
          (by intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))
          (by intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
      intro cowBad
      split
      · exact c.pure P none
      · apply StatePrefixEnsures.bind (c.branch P _ _)
        intro sgBad
        split
        · exact c.pure P none
        · apply StatePrefixEnsures.bind (c.branch P _ _)
          intro decryptBad
          split
          · exact c.pure P none
          · split
            · apply StatePrefixEnsures.bind (c.branch P _ _)
              intro trimBad
              split <;> exact c.pure P _
            · exact c.invariant P _

theorem decryptPacketPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop) (pkt : RxPacket) :
    ProductAmbientSpec I P (liftWGObserver (decryptPacketPrefix pkt)) (fun _ => P) := by
  simp only [decryptPacketPrefix, liftWGObserver_bind, liftWGObserver_pure]
  apply PrefixEnsures.bind (c.nativeStore P _ (by intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial)))
  intro noKey
  split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
  · exact c.pure P none
  · apply PrefixEnsures.bind (c.getKeypair_frame P pkt.keypair)
    intro k
    apply PrefixEnsures.bind (c.nativeStore P _ (decryptKeyReject_sameWGStore k))
    intro reject
    split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
    · apply PrefixEnsures.bind (c.getKeypair P pkt.keypair)
      intro fresh
      apply PrefixEnsures.bind (c.setKeypair P pkt.keypair
        {fresh with receiving := {fresh.receiving with isValid := false}})
      intro _
      exact c.pure P none
    · apply PrefixEnsures.bind (c.nativeStore P _ (by intro initial; exact hoare_liftAmbient (AmbientM.hiddenAlloc .skbCowDataRx) (fun w => wgStoreView w = initial)))
      intro cowOk
      apply PrefixEnsures.bind (c.nativeStore P _
        (orM_sameView
          (by intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))
          (by intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial))))
      intro cowBad
      split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
      · exact c.pure P none
      · apply PrefixEnsures.bind (c.nativeStore P _ (by intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial)))
        intro sgBad
        split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
        · exact c.pure P none
        · apply PrefixEnsures.bind (c.nativeStore P _ (by intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial)))
          intro decryptBad
          split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
          · exact c.pure P none
          · split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
            · apply PrefixEnsures.bind (c.nativeStore P _ (by intro initial; exact hoare_liftAmbient (AmbientM.branch _ _) (fun w => wgStoreView w = initial)))
              intro trimBad
              split <;> simpa only [liftWGObserver_pure] using c.pure P _
            · exact c.nativeStore P _ (by
                intro initial
                exact hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial))

theorem decryptPacketPrefix_spec (P : IdentityView → Prop) (pkt : RxPacket) :
    MixedSpec P (decryptPacketPrefix pkt) (fun _ => P) :=
  decryptPacketPrefix_spec_ambient mixedAmbient P pkt

theorem decryptPacketPrefix_preserves (pkt : RxPacket) :
    StatePrefixPreserves (fun h w _ => MixedInv h w) LifetimeEvent.Safe (decryptPacketPrefix pkt) :=
  AmbientContracts.drop (decryptPacketPrefix_spec_ambient mixedAmbient (fun _ => True) pkt)

/-- The rejection expression may fail while consuming its clock record.
That failure retains the successful keypair read, before any rejection update. -/
theorem decryptPacketPrefix_reject_failure (pkt : RxPacket) (w entered : WGWorld) (ambient enteredAmbient : Ambient)
    (h : List LifetimeEvent) (k : Keypair) (e : Stop)
    (hb : ((branch .decNoKeypair false : WG.M Bool).run w).run ambient = .ok ((false, entered), enteredAmbient))
    (hg : ((getKeypair pkt.keypair).run entered).run enteredAmbient = .ok ((k, entered), enteredAmbient))
    (hr : ((decryptKeyReject k).run entered).run enteredAmbient = .error e) :
    runStatePrefix (decryptPacketPrefix pkt) w ambient h =
      (.error e, h ++ [.keypair (.read pkt.keypair k.internalId)]) := by
  simp only [decryptPacketPrefix, runStatePrefix_bind, liftWGPrefix, runStatePrefix_lift, hb,
    Bool.false_eq_true, ↓reduceIte, getKeypairPrefix_run, hg, hr]

end Leanux.Proofs.WG.Lifetimes
