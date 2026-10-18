import Leanux.Proofs.WG.TimerDiscipline.InitiationTraversalSource
import Leanux.Proofs.WG.Noise.ResponseMacFrames
import Leanux.Proofs.WG.Noise.CreationTagClaims
import Leanux.Proofs.WG.Noise.TagSequenceModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.InitiationCaller
open Leanux Leanux.WG
open Leanux.Proofs.WG.TimerDiscipline Leanux.Proofs.Framing

/-- Creation success means a message was created, not that the later socket
send delivered it. -/
inductive Call where
  | rateLimited
  | noCreation (receipt : TagReceipt)
  | created (message : List UInt8) (receipt : TagReceipt)

def createObserved (pid : PeerId) : WG.M (Option (List UInt8) × TagReceipt) := do
  let before ← Campaign2.read
  let message ← createInitiation pid
  let after ← Campaign2.read
  return (message, ⟨.createInitiation pid, before, .created message, after⟩)

theorem createObserved_erases (pid : PeerId) :
    (do let created ← createObserved pid; pure created.1) = createInitiation pid := by
  simp only [createObserved, bind_assoc, pure_bind]
  funext g ambient
  change (((createInitiation pid).run g).run ambient >>= fun ((message, final), after) =>
    Except.ok ((message, final), after)) = ((createInitiation pid).run g).run ambient
  cases ((createInitiation pid).run g).run ambient <;> rfl

private def afterGuard (pid : PeerId) : WG.M (Call × Option (List UInt8)) := do
  let now ← hiddenClock64 .initLastSent
  modifyPeer pid fun p => {p with lastSentHandshake := now}
  let (created, receipt) ← createObserved pid
  if ← branch .initCreated created.isSome then
    let some msg := created | invariant "unreachable"
    let authenticated ← addMacToPacket pid msg
    return (.created msg receipt, some authenticated)
  return (.noCreation receipt, none)

/-- The original traversal prelude with one snapshot pair around the actual
creator. All branch calls, early exits and MAC processing remain in order. -/
def prelude (pid : PeerId) : WG.M (Call × Option (List UInt8)) := do
  if ← branchExpired .initRateLimited (← getPeer pid).lastSentHandshake REKEY_TIMEOUT (!·) then
    return (.rateLimited, none)
  afterGuard pid

theorem prelude_erases (pid : PeerId) :
    (do let out ← prelude pid; pure out.2) = initiationTraversalPrelude pid := by
  have update (f : Peer → Peer) : modifyPeer pid f =
      (do let p ← getPeer pid; setPeer pid (f p)) := rfl
  rw [show initiationTraversalPrelude pid = (do
    if ← branchExpired .initRateLimited (← getPeer pid).lastSentHandshake REKEY_TIMEOUT (!·) then return none
    let now ← hiddenClock64 .initLastSent
    setPeer pid { (← getPeer pid) with lastSentHandshake := now }
    let created ← (do let out ← createObserved pid; pure out.1)
    if ← branch .initCreated created.isSome then
      let some msg := created | invariant "unreachable"
      return some (← addMacToPacket pid msg)
    return none) by rw [createObserved_erases]; rfl]
  simp only [prelude, afterGuard, update, bind_assoc, pure_bind]
  congr 1
  funext peer
  congr 1
  funext limited
  cases limited <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc]
  congr 1
  funext now
  congr 1
  funext peer
  congr 1
  funext u
  congr 1
  funext created
  rcases created with ⟨message, receipt⟩
  congr 1
  funext made
  cases made <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind]
  cases message <;> simp only [bind_assoc, pure_bind]

/-- Normal results retain the creation receipt through the unchanged original
suffix. A later Stop remains a Stop and returns no partial receipt. -/
def observe (pid : PeerId) : WG.M Call := do
  let out ← prelude pid
  initiationTraversalSuffix pid out.2
  return out.1

theorem observe_erases (pid : PeerId) :
    (do let _ ← observe pid; pure ()) = sendHandshakeInitiation pid := by
  rw [← initiationTraversal_source, ← prelude_erases]
  simp only [observe, bind_assoc, pure_bind, bind_pure_unit]

/-- The final peer release may remove the peer; a receipt observes only its
creator cut, not the whole-worker exit. -/
def observeWorker (pid : PeerId) : WG.M Call := do
  let receipt ← observe pid
  WG.peerPut (some pid)
  return receipt

theorem observeWorker_erases (pid : PeerId) :
    (do let _ ← observeWorker pid; pure ()) = handshakeSendWorker pid := by
  rw [handshakeSendWorker, ← observe_erases]
  simp only [observeWorker, bind_assoc, pure_bind, bind_pure_unit]

end Leanux.Proofs.WG.Noise.InitiationCaller

namespace Leanux.Proofs.WG.Noise.InitiationCaller
open Leanux Leanux.WG
open Leanux.Proofs.WG.TimerDiscipline Leanux.Proofs.Framing

/-- The projected receipt is backed by the actual original creator run. -/
def ReceiptValid (pid : PeerId) (receipt : TagReceipt) : Prop :=
  ∃ g ambient message final after,
    ((createInitiation pid).run g).run ambient = .ok ((message, final), after) ∧
    receipt = ⟨.createInitiation pid, Campaign2.snapshot g ambient,
      .created message, Campaign2.snapshot final after⟩

def ReceiptFacts (pid : PeerId) (entry : Campaign2.Snapshot)
    (message : Option (List UInt8)) (receipt : TagReceipt) : Prop :=
  receipt.operation = .createInitiation pid ∧
  receipt.result = .created message ∧
  receipt.before.tagAt = entry.tagAt ∧
  ReceiptValid pid receipt ∧ TagReceiptEffect receipt

/-- The three normal paths distinguish rate limiting, creator refusal and a
created message. Refusal may retain non-tag writes by the creator. A created message need not have been delivered by the socket. -/
def CallFacts (pid : PeerId) (entry : Campaign2.Snapshot) : Call → Prop
  | .rateLimited => True
  | .noCreation receipt => ReceiptFacts pid entry none receipt
  | .created message receipt => ReceiptFacts pid entry (some message) receipt

theorem createObserved_facts (pid : PeerId) (entry : Campaign2.Snapshot) :
    Ensures (createObserved pid) (fun g => responseTagMap g.dev = entry.tagAt)
      (fun out _ => ReceiptFacts pid entry out.1 out.2) := by
  intro g ambient out final after pre run
  change (((createInitiation pid).run g).run ambient >>= fun ((message, current), inputs) =>
    Except.ok (((message, (⟨.createInitiation pid, Campaign2.snapshot g ambient,
      .created message, Campaign2.snapshot current inputs⟩ : TagReceipt)), current), inputs)) = _ at run
  cases actual : ((createInitiation pid).run g).run ambient with
  | error stop => rw [actual] at run; cases run
  | ok result =>
    obtain ⟨⟨message, current⟩, inputs⟩ := result
    rw [actual] at run
    cases run
    refine ⟨rfl, rfl, pre, ⟨g, ambient, message, final, after, actual, rfl⟩, ?_⟩
    exact createInitiation_tagMap_projected pid (Campaign2.snapshot g ambient)
      g ambient message final after rfl actual

theorem prelude_facts (pid : PeerId) (entry : Campaign2.Snapshot) :
    Ensures (prelude pid) (fun g => responseTagMap g.dev = entry.tagAt)
      (fun out _ => CallFacts pid entry out.1) := by
  let P : WGWorld → Prop := fun g => responseTagMap g.dev = entry.tagAt
  have read : Ensures (getPeer pid) P (fun _ => P) := by
    intro g a p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P)
      g a p final after pre run).1
  have pureFacts (call : Call) (message : Option (List UInt8))
      (fact : CallFacts pid entry call) :
      Ensures (pure (call, message) : WG.M _) P (fun out _ => CallFacts pid entry out.1) := by
    intro g a out final after pre run
    cases run
    exact fact
  unfold prelude afterGuard
  refine ensures_bind _ _ read ?_
  intro p
  have expired : Ensures
      (branchExpired .initRateLimited p.lastSentHandshake REKEY_TIMEOUT (!·)) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr
      (((branchExpired_sameWGWorld _ _ _ (!·)).factor (fun g => responseTagMap g.dev)) entry.tagAt)
  refine ensures_bind _ _ expired ?_
  intro limited
  cases limited
  · simp only [Bool.false_eq_true, ite_false]
    refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
    · intro g a now final after pre run
      exact (ResponseCaller.clock_tag_frame _ g a now final after run).trans pre
    · intro now
      refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
      · intro g a u final after pre run
        exact (ResponseCaller.lastSent_tag_frame pid now g a u final after run).trans pre
      · intro u
        refine ensures_bind _ _ (createObserved_facts pid entry) ?_
        intro out
        rcases out with ⟨created, receipt⟩
        refine ensures_bind _ _
          ((ensures_iff _ _ _).mpr (Config.branch_state_spec
            (fun _ : WGWorld => ReceiptFacts pid entry created receipt) .initCreated created.isSome)) ?_
        intro made
        intro g a result final after pre run
        have madeEq := pre.1
        subst made
        cases created with
        | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, ite_false] at run
          cases run
          exact pre.2
        | some msg =>
          simp only [Option.isSome_some, ite_true] at run
          change (((addMacToPacket pid msg).run g).run a >>= fun ((authenticated, current), inputs) =>
            Except.ok (((Call.created msg receipt, some authenticated), current), inputs)) = _ at run
          cases mac : ((addMacToPacket pid msg).run g).run a with
          | error stop => rw [mac] at run; cases run
          | ok pair =>
            obtain ⟨⟨authenticated, current⟩, inputs⟩ := pair
            rw [mac] at run
            cases run
            exact pre.2
  · simp only [ite_true]
    exact pureFacts .rateLimited none True.intro

theorem observe_facts (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observe pid) (fun s => s.tagAt = entry.tagAt)
      (fun call _ => CallFacts pid entry call) := by
  change Ensures _ (fun (g : WGWorld) => responseTagMap g.dev = entry.tagAt) _
  unfold observe
  refine ensures_bind _ _ (prelude_facts pid entry) ?_
  intro out
  refine ensures_bind (Q := fun _ _ => CallFacts pid entry out.1) _ _ ?_ ?_
  · intro g ambient u final after pre run
    exact pre
  · intro u
    intro g ambient call final after pre run
    cases run
    exact pre

theorem observeWorker_facts (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observeWorker pid) (fun s => s.tagAt = entry.tagAt)
      (fun call _ => CallFacts pid entry call) := by
  change Ensures _ (fun (g : WGWorld) => responseTagMap g.dev = entry.tagAt) _
  unfold observeWorker
  refine ensures_bind _ _ (observe_facts pid entry) ?_
  intro call
  refine ensures_bind (Q := fun _ _ => CallFacts pid entry call) _ _ ?_ ?_
  · intro g ambient u final after pre run
    exact pre
  · intro u
    intro g ambient result final after pre run
    cases run
    exact pre

end Leanux.Proofs.WG.Noise.InitiationCaller

namespace Leanux.Proofs.WG.Noise.InitiationCaller
open Leanux Leanux.WG
open Leanux.Proofs.WG.TimerDiscipline Leanux.Proofs.Framing

def Call.isRateLimited : Call → Bool
  | .rateLimited => true
  | .noCreation _ | .created _ _ => false

/-- The actual first guard, including the peer read and recorded age test. -/
def rateGuard (pid : PeerId) : WG.M Bool := do
  let p ← getPeer pid
  branchExpired .initRateLimited p.lastSentHandshake REKEY_TIMEOUT (!·)

private theorem prelude_guard_source (pid : PeerId) :
    prelude pid = (do
      if ← rateGuard pid then return (.rateLimited, none)
      afterGuard pid) := by
  simp only [prelude, rateGuard, afterGuard, bind_assoc]

private theorem afterGuard_not_limited (pid : PeerId) :
    Ensures (afterGuard pid) (fun _ => True)
      (fun out _ => out.1.isRateLimited = false) := by
  have any {α : Type} (action : WG.M α) :
      Ensures action (fun _ => True) (fun _ _ => True) := by
    intro g ambient x final after pre run
    trivial
  have pureNo (call : Call) (message : Option (List UInt8))
      (fact : call.isRateLimited = false) :
      Ensures (pure (call, message) : WG.M _) (fun _ => True)
        (fun out _ => out.1.isRateLimited = false) := by
    intro g ambient x final after pre run
    cases run
    exact fact
  unfold afterGuard
  refine ensures_bind _ _ (any _) ?_
  intro now
  refine ensures_bind _ _ (any _) ?_
  intro u
  refine ensures_bind _ _ (any _) ?_
  intro out
  rcases out with ⟨created, receipt⟩
  refine ensures_bind _ _ (any _) ?_
  intro made
  cases made
  · simp only [Bool.false_eq_true, ite_false]
    exact pureNo (.noCreation receipt) none rfl
  · simp only [ite_true]
    cases created with
    | none =>
      refine ensures_bind _ _ (any _) ?_
      intro impossible
      exact pureNo (.noCreation receipt) none rfl
    | some msg =>
      refine ensures_bind _ _ (any _) ?_
      intro authenticated
      exact pureNo (.created msg receipt) (some authenticated) rfl

theorem prelude_rate_run (pid : PeerId) (g : WGWorld) (ambient : Ambient)
    (out : Call × Option (List UInt8)) (final : WGWorld) (after : Ambient)
    (run : ((prelude pid).run g).run ambient = .ok ((out, final), after)) :
    ∃ middle inputs, ((rateGuard pid).run g).run ambient =
      .ok ((out.1.isRateLimited, middle), inputs) := by
  rw [prelude_guard_source] at run
  change (((rateGuard pid).run g).run ambient >>= fun ((limited, middle), inputs) =>
    (((if limited then pure (Call.rateLimited, none) else afterGuard pid) : WG.M _).run middle).run inputs) = _ at run
  cases actual : ((rateGuard pid).run g).run ambient with
  | error stop => rw [actual] at run; cases run
  | ok pair =>
    obtain ⟨⟨limited, middle⟩, inputs⟩ := pair
    rw [actual] at run
    simp only [bind, Except.bind] at run
    cases limited
    · have notLimited := afterGuard_not_limited pid middle inputs out final after True.intro run
      exact ⟨middle, inputs, by simp only [notLimited]⟩
    · change Except.ok (((Call.rateLimited, none), middle), inputs) = _ at run
      cases run
      exact ⟨final, after, rfl⟩

/-- An actual initial-guard execution, projected at entry. The source theorem
constructs this witness from the same sender run, not a reconstructed state. -/
def RateObserved (pid : PeerId) (entry : Campaign2.Snapshot) (call : Call) : Prop :=
  ∃ g ambient middle inputs,
    Campaign2.snapshot g ambient = entry ∧
    ((rateGuard pid).run g).run ambient =
      .ok ((call.isRateLimited, middle), inputs)

theorem observe_rate (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observe pid) (fun s => s = entry)
      (fun call _ => RateObserved pid entry call) := by
  intro g ambient call final after pre run
  change (((prelude pid).run g).run ambient >>= fun ((out, middle), inputs) =>
    (((initiationTraversalSuffix pid out.2).run middle).run inputs >>= fun ((_, current), rest) =>
      Except.ok ((out.1, current), rest))) = _ at run
  cases prefixRun : ((prelude pid).run g).run ambient with
  | error stop => rw [prefixRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨out, middle⟩, inputs⟩ := pair
    rw [prefixRun] at run
    simp only [bind, Except.bind] at run
    cases suffix : ((initiationTraversalSuffix pid out.2).run middle).run inputs with
    | error stop => rw [suffix] at run; cases run
    | ok pair =>
      obtain ⟨⟨u, current⟩, rest⟩ := pair
      rw [suffix] at run
      cases run
      obtain ⟨cut, cutInputs, guard⟩ := prelude_rate_run pid g ambient out middle inputs prefixRun
      exact ⟨g, ambient, cut, cutInputs, pre, guard⟩

theorem observeWorker_rate (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observeWorker pid) (fun s => s = entry)
      (fun call _ => RateObserved pid entry call) := by
  intro g ambient call final after pre run
  change (((observe pid).run g).run ambient >>= fun ((out, middle), inputs) =>
    (((WG.peerPut (some pid)).run middle).run inputs >>= fun ((_, current), rest) =>
      Except.ok ((out, current), rest))) = _ at run
  cases sender : ((observe pid).run g).run ambient with
  | error stop => rw [sender] at run; cases run
  | ok pair =>
    obtain ⟨⟨out, middle⟩, inputs⟩ := pair
    rw [sender] at run
    simp only [bind, Except.bind] at run
    cases release : ((WG.peerPut (some pid)).run middle).run inputs with
    | error stop => rw [release] at run; cases run
    | ok pair =>
      obtain ⟨⟨u, current⟩, rest⟩ := pair
      rw [release] at run
      cases run
      exact observe_rate pid entry g ambient call middle inputs pre sender

end Leanux.Proofs.WG.Noise.InitiationCaller
