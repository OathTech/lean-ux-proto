import Leanux.Proofs.WG.Lifetimes.Enqueue

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Decryption observations. Only the original access-free rejection expression
is factored; both keypair reads and the validity update remain explicit. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def decryptKeyReject (k : Keypair) : M Bool :=
  WG.orM (branch .decKeyInvalid !k.receiving.isValid) do
    WG.orM (branchExpired .decKeyExpired k.receiving.birthdate REJECT_AFTER_TIME)
      (branchCmp .decCounterLimit (k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES)
        k.receivingCounter.counter REJECT_AFTER_MESSAGES)

theorem orM_sameKernel (ha : SameKernel a) (hb : SameKernel b) : SameKernel (WG.orM a b) := by
  unfold WG.orM
  apply sameKernel_bind ha
  intro yes
  split
  · exact sameKernel_pure _
  · exact hb

theorem decryptKeyReject_sameKernel (k : Keypair) : SameKernel (decryptKeyReject k) := by
  unfold decryptKeyReject
  apply orM_sameKernel (sameKernel_branch _ _)
  apply orM_sameKernel
  · exact branchExpired_sameKernel _ _ _
  · exact branchCmp_sameKernel _ _ _ _

def decryptPacketPrefix (pkt : RxPacket) : MixedM (Option RxPacket) := do
  if ← liftPrefix (branch .decNoKeypair false) then return none
  let k ← getKeypairPrefix pkt.keypair
  let reject ← liftPrefix (decryptKeyReject k)
  if reject then
    let k ← getKeypairPrefix pkt.keypair
    setKeypairPrefix pkt.keypair { k with receiving := { k.receiving with isValid := false } }
    return none
  let nonce := u64le pkt.bytes 8
  let cowOk ← liftPrefix (hiddenAlloc .skbCowDataRx)
  if ← liftPrefix (WG.orM (branch .decCowDataFailed !cowOk) (branch .decTooManyFrags false)) then return none
  if ← liftPrefix (branch .decSgvecFailed false) then return none
  let plain := aeadDecrypt k.receiving.key (counterNonce nonce) (pkt.bytes.drop 16) []
  if ← liftPrefix (branch .decDecryptFailed plain.isNone) then return none
  let some bytes := plain | liftPrefix (invariant "unreachable")
  if ← liftPrefix (branch .decTrimFailed false) then return none
  return some { pkt with nonce, bytes }

theorem decryptPacketPrefix_erases (pkt : RxPacket) :
    ErasesPrefix (decryptPacketPrefix pkt) (decryptPacket pkt) := by
  unfold decryptPacketPrefix decryptPacket decryptKeyReject
  repeat' first
    | rfl
    | exact getKeypairPrefix_erases _
    | exact setKeypairPrefix_erases _ _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | intro x
    | split
  all_goals simp_all [runPrefix_pure, runPrefix_lift]

theorem decryptPacketPrefix_spec_ambient (c : AmbientContracts I) (P : IdentityView → Prop) (pkt : RxPacket) :
    AmbientSpec I P (decryptPacketPrefix pkt) (fun _ => P) := by
  unfold decryptPacketPrefix
  apply PrefixEnsures.bind (c.branch P _ _)
  intro noKey
  split
  · exact c.pure P none
  · apply PrefixEnsures.bind (c.getKeypair_frame P pkt.keypair)
    intro k
    apply PrefixEnsures.bind (c.kernel P _ (decryptKeyReject_sameKernel k))
    intro reject
    split
    · apply PrefixEnsures.bind (c.getKeypair P pkt.keypair)
      intro fresh
      apply PrefixEnsures.bind (c.setKeypair P pkt.keypair
        {fresh with receiving := {fresh.receiving with isValid := false}})
      intro _
      exact c.pure P none
    · apply PrefixEnsures.bind (c.kernel P _ (hiddenAlloc_sameKernel .skbCowDataRx))
      intro cowOk
      apply PrefixEnsures.bind (c.kernel P _
        (orM_sameKernel (sameKernel_branch _ _) (sameKernel_branch _ _)))
      intro cowBad
      split
      · exact c.pure P none
      · apply PrefixEnsures.bind (c.branch P _ _)
        intro sgBad
        split
        · exact c.pure P none
        · apply PrefixEnsures.bind (c.branch P _ _)
          intro decryptBad
          split
          · exact c.pure P none
          · split
            · apply PrefixEnsures.bind (c.branch P _ _)
              intro trimBad
              split <;> exact c.pure P _
            · exact c.invariant P _

theorem decryptPacketPrefix_spec (P : IdentityView → Prop) (pkt : RxPacket) :
    MixedSpec P (decryptPacketPrefix pkt) (fun _ => P) :=
  decryptPacketPrefix_spec_ambient mixedAmbient P pkt

theorem decryptPacketPrefix_preserves (pkt : RxPacket) :
    PrefixPreserves MixedInv LifetimeEvent.Safe (decryptPacketPrefix pkt) :=
  mixed_drop (decryptPacketPrefix_spec (fun _ => True) pkt)

/-- The rejection expression may fail while consuming its clock record.
That failure retains the successful keypair read, before any rejection update. -/
theorem decryptPacketPrefix_reject_failure (pkt : RxPacket) (w entered : World)
    (h : List LifetimeEvent) (k : Keypair) (e : Stop)
    (hb : (branch .decNoKeypair false).run w = .ok (false, entered))
    (hg : (getKeypair pkt.keypair).run entered = .ok (k, entered))
    (hr : (decryptKeyReject k).run entered = .error e) :
    runPrefix (decryptPacketPrefix pkt) w h =
      (.error e, h ++ [.keypair (.read pkt.keypair k.internalId)]) := by
  simp only [decryptPacketPrefix, runPrefix_bind, runPrefix_lift, hb,
    Bool.false_eq_true, ↓reduceIte, getKeypairPrefix_run, hg, hr]

end Leanux.Proofs.WG.Lifetimes
