import Leanux.Proofs.WG.Roaming.InitiationOutFrames
import Leanux.Proofs.WG.Roaming.InitiationLookupSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def initiationFinish (msg : List UInt8) (identity : StaticIdentity) (s : Key)
    (pid : PeerId) (lookup : InitiationLookup) (dhPeer : Peer) (beforeDh : Campaign2.Snapshot)
    (ckSs t hashT : List UInt8) : WG.M (Option InitiationConsumed) := do
  let peer := some pid
  let e := (msg.drop 8).take 32
  let fail (peer : Option PeerId) : WG.M (Option InitiationConsumed) := do
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
def initiationConsume (msg : List UInt8) : WG.M (Option InitiationConsumed) := do
  let fail (peer : Option PeerId) : WG.M (Option InitiationConsumed) := do
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
  have bind_if {α β : Type} (condition : Prop) [Decidable condition]
      (yes no : WG.M α) (next : α → WG.M β) :
      ((if condition then yes else no) >>= next) =
        if condition then yes >>= next else no >>= next := by split <;> rfl
  have read_drop {α : Type} (a : WG.M α) : (do let _ ← Campaign2.read; a) = a := rfl
  have read_eq {α : Type} (next : Campaign2.Snapshot → WG.M α) (a : WG.M α)
      (same : ∀ view, next view = a) : (Campaign2.read >>= next) = a := by
    have fn : next = fun _ => a := funext same
    rw [fn]
    rfl
  simp only [initiationConsume, initiationFinish, consumeInitiation, initiationOut, initiationPeer,
    bind_assoc, pure_bind, bind_if, Option.map_none]
  congr 1
  funext d
  congr 1
  funext noIdentity
  cases noIdentity <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals try rfl
  congr 1
  funext ephemeral
  rcases ephemeral with ⟨ck, hash⟩
  congr 1
  funext es
  congr 1
  funext failed
  cases failed <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals try rfl
  cases es with
  | none => rfl
  | some pair =>
    rcases pair with ⟨ck, key⟩
    simp only [bind_assoc]
    congr 1
    funext st
    congr 1
    funext failed
    cases failed <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      bind_assoc, pure_bind, bind_if]
    all_goals try rfl
    cases st with
    | none => rfl
    | some pair =>
      rcases pair with ⟨plain, hash⟩
      simp only [bind_assoc]
      rw [← initiationLookup_bind]
      congr 1
      funext lookup
      congr 1
      funext missing
      cases missing <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        bind_assoc, pure_bind, bind_if]
      all_goals try rfl
      cases hp : lookup.result with
      | none => rfl
      | some pid =>
        try simp only [bind_assoc]
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
          bind_assoc, pure_bind, bind_if]
        all_goals try rfl
        cases ss with
        | none => rfl
        | some pair =>
          rcases pair with ⟨ck, key⟩
          simp only [bind_assoc]
          congr 1
          funext ts
          congr 1
          funext failed
          cases failed <;> simp only [Bool.false_eq_true, ite_false, ite_true,
            bind_assoc, pure_bind, bind_if]
          all_goals try rfl
          cases ts with
          | none => rfl
          | some pair =>
            rcases pair with ⟨timestamp, hash⟩
            simp only [bind_assoc, pure_bind, bind_if, Option.map_none, Option.map_some, read_drop]


/-- Erasing the native certificate also preserves the complete actual product
execution, including every rejected prefix and Stop. -/
theorem initiationConsume_lift_erase (msg : List UInt8) :
    (do let out ← liftWG (initiationConsume msg); pure (initiationPeer out)) =
      liftWG (consumeInitiation msg) := by
  rw [← initiationConsume_erase]
  funext w
  dsimp only [liftWG, StateT.run, StateT.bind, StateT.pure, StateT.map,
    Bind.bind, Pure.pure, Functor.map, Except.bind, Except.pure]
  cases run : ((initiationConsume msg).run w.wg).run w.ambient with
  | error err => simp only [StateT.run] at run; rw [run]
  | ok pair =>
    rcases pair with ⟨⟨value, current⟩, after⟩
    simp only [StateT.run] at run
    rw [run]

end Leanux.Proofs.WG.Roaming
