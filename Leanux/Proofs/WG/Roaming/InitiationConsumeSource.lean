import Leanux.Proofs.WG.Roaming.InitiationCryptoSource
import Leanux.Proofs.WG.Roaming.InitiationLookupSource
import Leanux.Proofs.WG.Roaming.PollEndpointSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The original consumer's exit helper, including its failed reference put. -/
def initiationOut (peer ret : Option PeerId) : M (Option PeerId) := do
  if ← branch .consumeFailedPut ret.isNone then peerPut peer
  return ret

theorem initiationOut_effect (peer ret : Option PeerId) (initial : Kernel) :
    ⦃fun w => ⌜w.k = initial⌝⦄ initiationOut peer ret
      ⦃⇓? result w => ⌜result = ret ∧ (ret.isSome = true → w.k = initial)⌝⦄ := by
  have hp : ⦃fun _ => ⌜True⌝⦄ peerPut peer ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro w result final pre run
    trivial
  cases ret <;> mvcgen [initiationOut, branch, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

def initiationFinish (msg : List UInt8) (identity : StaticIdentity) (s : Key)
    (pid : PeerId) (lookup : InitiationLookup) (dhPeer : Peer) (beforeDh : Campaign2.Snapshot)
    (ckSs t hashT : List UInt8) : M (Option InitiationConsumed) := do
  let peer := some pid
  let e := (msg.drop 8).take 32
  let fail (peer : Option PeerId) : M (Option InitiationConsumed) := do
    let _ ← initiationOut peer none
    return none
  let p ← getPeer pid
  let beforeChecks ← Campaign2.read
  let replay := memcmp t p.latestTimestamp != .gt
  let floodLhs : Int64 := p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64
  let now ← hiddenClock64 .floodNow
  if ← WG.orM (branch .consumeReplay replay) (branchCmp .consumeFlood (floodLhs > now) floodLhs.toInt now.toInt) then
    return ← fail peer
  setPeer pid { (← getPeer pid) with remoteEphemeral := e }
  if ← branch .consumeNewerTimestamp (memcmp t p.latestTimestamp == .gt) then
    setPeer pid { (← getPeer pid) with latestTimestamp := t }
  setPeer pid { (← getPeer pid) with hash := hashT, chainingKey := ckSs, remoteIndex := u32le msg 4 }
  let consumption ← hiddenClock64 .consumptionNow
  let last := (← getPeer pid).lastInitiationConsumption
  let diff : Int64 := last - consumption
  if ← branchCmp .consumeLaterTime (diff < 0) diff.toInt 0 then
    setPeer pid { (← getPeer pid) with lastInitiationConsumption := consumption }
  setPeer pid { (← getPeer pid) with handshakeState := HANDSHAKE_CONSUMED_INITIATION }
  let _ ← initiationOut peer (some pid)
  return some ⟨identity, s, t, pid, lookup, dhPeer, beforeDh, p, beforeChecks, now,
    consumption, ← Campaign2.read⟩

/-- Decorate the actual consumer's reads and successful commit. Both failed
decrypt exits and the post-lookup release paths keep the original out helper. -/
def initiationConsume (msg : List UInt8) : M (Option InitiationConsumed) := do
  let fail (peer : Option PeerId) : M (Option InitiationConsumed) := do
    let _ ← initiationOut peer none
    return none
  let identity := (← getDev).staticIdentity
  if ← branch .consumeNoIdentity !identity.hasIdentity then return ← fail none
  let hash := noiseHash (handshakeInitHash ++ identity.staticPublic)
  let e := (msg.drop 8).take 32
  let (ck, hash) ← messageEphemeral true e handshakeInitChainingKey hash
  let es ← mixDh true ck identity.staticPrivate e
  if ← branch .consumeEsFailed es.isNone then return ← fail none
  let some (ck, key) := es | invariant "unreachable"
  let st ← messageDecrypt ((msg.drop 40).take 48) key hash
  if ← branch .consumeStaticFailed st.isNone then return ← fail none
  let some (s, hash) := st | invariant "unreachable"
  let lookup ← initiationLookup s
  let peer := lookup.result
  if ← branch .consumeNoPeer peer.isNone then return ← fail none
  let some pid := peer | invariant "unreachable"
  let dhPeer ← getPeer pid
  let beforeDh ← Campaign2.read
  let ss ← mixPrecomputedDh ck dhPeer.precomputedStaticStatic
  if ← branch .consumeSsFailed ss.isNone then return ← fail peer
  let some (ckSs, key) := ss | invariant "unreachable"
  let ts ← messageDecrypt ((msg.drop 88).take 28) key hash
  if ← branch .consumeTimestampFailed ts.isNone then return ← fail peer
  let some (t, hashT) := ts | invariant "unreachable"
  initiationFinish msg identity s pid lookup dhPeer beforeDh ckSs t hashT

def initiationPeer (out : Option InitiationConsumed) : Option PeerId := out.map (·.pid)

/-- Exact original consumer, with all rejection and error paths retained. -/
theorem initiationConsume_erase (msg : List UInt8) :
    (do let out ← initiationConsume msg; pure (initiationPeer out)) = consumeInitiation msg := by
  have read_drop {α : Type} (a : M α) : (do let _ ← Campaign2.read; a) = a := rfl
  have read_eq {α : Type} (next : Campaign2.Snapshot → M α) (a : M α)
      (same : ∀ view, next view = a) : (Campaign2.read >>= next) = a := by
    have fn : next = fun _ => a := funext same
    rw [fn]
    rfl
  simp only [initiationConsume, initiationFinish, consumeInitiation, initiationOut, initiationPeer,
    bind_assoc, pure_bind, bind_if, bind_option, invariant_bind, Option.map_none,
    Option.map_some, read_drop]
  congr 1
  funext d
  congr 1
  funext noIdentity
  cases noIdentity <;> simp only [Bool.false_eq_true, ite_false, ite_true,
    bind_assoc, pure_bind, bind_if, bind_option, invariant_bind, Option.map_none,
    Option.map_some, read_drop]
  all_goals try rfl
  congr 1
  funext ephemeral
  rcases ephemeral with ⟨ck, hash⟩
  congr 1
  funext es
  congr 1
  funext failed
  cases failed <;> simp only [Bool.false_eq_true, ite_false, ite_true,
    bind_assoc, pure_bind, bind_if, bind_option, invariant_bind]
  all_goals try rfl
  cases es with
  | none => rfl
  | some pair =>
    rcases pair with ⟨ck, key⟩
    simp only [bind_assoc, pure_bind]
    congr 1
    funext st
    congr 1
    funext failed
    cases failed <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      bind_assoc, pure_bind, bind_if, bind_option, invariant_bind]
    all_goals try rfl
    cases st with
    | none => rfl
    | some pair =>
      rcases pair with ⟨plain, hash⟩
      simp only [bind_assoc, pure_bind]
      rw [← initiationLookup_bind]
      congr 1
      funext lookup
      congr 1
      funext missing
      cases missing <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        bind_assoc, pure_bind, bind_if, bind_option, invariant_bind]
      all_goals try rfl
      cases hp : lookup.result with
      | none => rfl
      | some pid =>
        try simp only [bind_assoc, pure_bind, read_drop]
        congr 1
        funext peer
        apply read_eq
        intro beforeDh
        try simp only [bind_assoc, pure_bind]
        congr 1
        funext ss
        congr 1
        funext failed
        cases failed <;> simp only [Bool.false_eq_true, ite_false, ite_true,
          bind_assoc, pure_bind, bind_if, bind_option, invariant_bind]
        all_goals try rfl
        cases ss with
        | none => rfl
        | some pair =>
          rcases pair with ⟨ck, key⟩
          simp only [bind_assoc, pure_bind]
          congr 1
          funext ts
          congr 1
          funext failed
          cases failed <;> simp only [Bool.false_eq_true, ite_false, ite_true,
            bind_assoc, pure_bind, bind_if, bind_option, invariant_bind]
          all_goals try rfl
          cases ts with
          | none => rfl
          | some pair =>
            rcases pair with ⟨timestamp, hash⟩
            simp only [bind_assoc, pure_bind, bind_if, Option.map_none, Option.map_some, read_drop]

theorem initiationFinish_facts (msg : List UInt8) (identity : StaticIdentity) (s : Key)
    (pid : PeerId) (lookup : InitiationLookup) (dhPeer : Peer) (beforeDh : Campaign2.Snapshot)
    (ck timestamp hash : List UInt8) :
    Ensures (initiationFinish msg identity s pid lookup dhPeer beforeDh ck timestamp hash)
      (fun _ => True)
      (fun result w => ∀ cut, result = some cut →
        cut.committed = Campaign2.snapshot w ∧ cut.identity = identity ∧
        cut.staticPlain = s ∧ cut.timestamp = timestamp ∧ cut.pid = pid ∧
        cut.lookup = lookup ∧ cut.dhPeer = dhPeer ∧ cut.beforeDh = beforeDh ∧
        InitiationCommitFacts msg ck hash cut) := by
  rw [ensures_iff]
  have snapshot_peer (w : World) (pid : PeerId) :
      (Campaign2.snapshot w).peerAt pid = (w.k.wg.bind fun d => d.peers[pid]?) := rfl
  have hg := fun initial => getPeer_spec pid (fun w => peerAt w pid = initial)
  have hs (p : Peer) : ⦃fun w => ⌜(peerAt w pid).isSome⌝⦄ setPeer pid p
      ⦃⇓? _ w => ⌜peerAt w pid = some p⌝⦄ := by
    have setter := setPeer_spec pid p (fun q => q = p)
    mvcgen [setter]
    all_goals simp_all
  have hh := fun initial site => hiddenClock64_kernel_spec
    (fun k => (k.wg.bind fun d => d.peers[pid]?) = initial) site
  have hr := fun initial => read_snapshot (fun w => peerAt w pid = initial)
  have ho := initiationOut_effect
  mvcgen -trivial [initiationFinish, branch, branchCmp, WG.orM, invariant, hg, hs, hh, hr, ho]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [InitiationCommitFacts, initiationEphemeral, snapshot_peer,
    peerAt, ExceptConds.true]
  all_goals try simp_all only [heq_eq_eq]
  all_goals repeat intro
  all_goals try subst_vars
  all_goals try simp_all [snapshot_peer]
  all_goals grind only [Option.isSome_some]

theorem initiationConsume_facts (msg : List UInt8) :
    Ensures (initiationConsume msg) (fun _ => True)
      (fun result w => ∀ cut, result = some cut →
        cut.committed = Campaign2.snapshot w ∧ InitiationConsumedFacts msg cut) := by
  rw [ensures_iff]
  have snapshot_peer (w : World) (pid : PeerId) :
      (Campaign2.snapshot w).peerAt pid = (w.k.wg.bind fun d => d.peers[pid]?) := rfl
  have he := fun e ck hash => responseEphemeral_returns e ck hash (fun _ => True)
  have hd := fun ck priv pub => initiationDh_returns ck priv pub (fun _ => True)
  have hm := fun sealed key hash => responseDecrypt_returns sealed key hash (fun _ => True)
  have hs := fun ck precomputed => initiationPrecomputed_returns ck precomputed (fun _ => True)
  have hl := fun key => (ensures_iff _ _ _).mp (initiationLookup_facts key)
  have hr := fun initial => read_snapshot (fun w => w.k = initial)
  have ht := fun identity s pid lookup dhPeer beforeDh ck timestamp hash =>
    (ensures_iff _ _ _).mp (initiationFinish_facts msg identity s pid lookup dhPeer beforeDh ck timestamp hash)
  have hp (peer : Option PeerId) : ⦃fun _ => ⌜True⌝⦄ peerPut peer ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro w x final pre run
    trivial
  have ho := initiationOut_effect
  mvcgen [initiationConsume, getPeer, getDev, getK,
    branch, invariant, he, hd, hm, hs, hl, hr, ht, ho]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [InitiationConsumedFacts, initiationEphemeral,
    initiationEsInput, initiationDh, initiationEsChain, initiationStaticKey,
    initiationStaticAad, initiationTimestampAad, snapshot_peer]
  all_goals grind

end Leanux.Proofs.WG.Roaming
