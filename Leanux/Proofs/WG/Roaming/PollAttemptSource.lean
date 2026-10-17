import Leanux.Proofs.WG.Roaming.PollAttemptModel
import Leanux.Proofs.WG.Roaming.PollEndpointSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Campaign2 Std.Do

def pollAttemptPrefix (pid : PeerId) : Leanux.M PollAttemptPrepared := do
  let (first, q) ← (← getPeer pid).rxQueue.peek
  setPeer pid { (← getPeer pid) with rxQueue := q }
  let go ← WG.andM (branch .rxPollPacket first.isSome) do
    let some f := first | invariant "unreachable"
    branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted)
  if !go then return .drained
  let some id := first | invariant "unreachable"
  let beforeRead ← Campaign2.Product.read
  let pkt ← getRxSkb id
  if pkt.peer != pid then invariant "a packet on another peer's rx_queue"
  setPeer pid { (← getPeer pid) with rxQueue := (← getPeer pid).rxQueue.dropPeeked }
  if ← branch .rxPollNotCrypted (pkt.state != .crypted) then return .rejected id pkt
  let beforeCounter ← Campaign2.Product.read
  let valid ← counterValidate pkt.keypair pkt.nonce
  let afterCounter ← Campaign2.Product.read
  if ← branch .rxPollCounterInvalid !valid then return .rejected id pkt
  let endpoint ← endpointFromSkb pkt.source
  if ← branch .rxPollEndpointFailed endpoint.isNone then return .rejected id pkt
  let some e := endpoint | invariant "unreachable"
  let beforeSetter ← Campaign2.Product.read
  return .endpoint ⟨id, pkt, e, beforeRead, beforeCounter, afterCounter,
    .ok (valid, afterCounter), beforeSetter⟩

def pollAttemptSuffix (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (state : PollState)
    (prepared : PollAttemptPrepared) : Leanux.M (ForInStep PollState) := do
  match prepared with
  | .drained => return .done (state.1, state.2.1, true)
  | .rejected id pkt => pollPacketCleanup pid budget state id pkt true
  | .endpoint cut =>
    setPeerEndpoint pid cut.endpoint
    let mut gro := state.2.1
    for inner in (← consumeDataAfterEndpoint pid cut.packet).toList do
      gro ← napiGroReceive toStack gro inner
    pollPacketCleanup pid budget (state.1, gro, state.2.2) cut.id cut.packet false

theorem pollStep_attempt_source (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (turn : Nat) (state : PollState) :
    pollStep pid budget toStack turn state =
      (pollAttemptPrefix pid >>= pollAttemptSuffix pid budget toStack state) := by
  -- Local forms of campaign 1's Framing.liftWG_run and liftWG_bind.
  have liftWG_run_variant {α : Type} (a : WG.M α) (w) :
      (liftWG a).run w = ((a.run w.wg).run w.ambient).map
        (fun ((x, g), ambient) => (x, {w with wg := g, ambient})) := by
    unfold liftWG StateT.run
    cases a w.wg w.ambient <;> rfl
  have liftWG_bind_variant {α β : Type} (a : WG.M α) (f : α → WG.M β) :
      (monadLift (a >>= f) : Leanux.M β) =
        (do let x ← (monadLift a : Leanux.M α); monadLift (f x)) := by
    funext w
    change (liftWG (a >>= f)).run w = (liftWG a >>= fun x => liftWG (f x)).run w
    rw [liftWG_run_variant]
    simp only [StateT.run_bind]
    rw [liftWG_run_variant]
    cases hr : (a.run w.wg).run w.ambient with
    | error e => rfl
    | ok out =>
      rcases out with ⟨⟨x, g⟩, ambient⟩
      simp only [Except.map]
      exact (liftWG_run_variant (f x) {w with wg := g, ambient}).symm
  simp only [pollStep, pollAttemptPrefix, pollAttemptSuffix,
    consumeDataDone_source, bind_assoc, pure_bind, bind_if, invariant_bind]
  congr 1
  funext peer
  congr 1
  funext peek
  rcases peek with ⟨first, queue⟩
  congr 1
  funext peer
  congr 1
  funext stepUnit
  congr 1
  funext go
  cases go <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
  all_goals try rfl
  cases first <;> simp only [bind_assoc, pure_bind, bind_if, invariant_bind, pollAttemptSuffix, pollPacketCleanup]
  all_goals try rfl
  apply Eq.trans (read_ignore _).symm
  congr 1
  funext beforeRead
  congr 1
  funext pkt
  split <;> try rfl
  all_goals try rfl
  congr 1
  funext peer
  congr 1
  funext peer2
  congr 1
  funext stepUnit
  congr 1
  funext crypted
  cases crypted <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
  all_goals try rfl
  apply Eq.trans (read_ignore _).symm
  congr 1
  funext beforeCounter
  congr 1
  funext valid
  apply Eq.trans (read_ignore _).symm
  congr 1
  funext afterCounter
  congr 1
  funext rejected
  cases rejected <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
  all_goals try rfl
  congr 1
  funext endpoint
  congr 1
  funext failed
  cases failed <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
  all_goals try rfl
  cases endpoint <;> simp only [bind_assoc, pure_bind, invariant_bind, pollAttemptSuffix, pollPacketCleanup, read_ignore]
  all_goals first | rfl | simp only [liftWG_bind_variant, bind_assoc]

end Leanux.Proofs.WG.Roaming
