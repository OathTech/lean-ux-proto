import Leanux.Proofs.WG.Roaming.ResponseConsumeSource
import Leanux.Proofs.WG.Roaming.PollEndpointSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The inspection and the original lookup start at exactly the same state.
The original lookup executes once on the continuing path. -/
def responseLookupRead (msg : List UInt8) : M ResponseLookupRead := do
  let before ← Campaign2.read
  let observed ← Campaign2.inspect (indexLookup [.handshake] (u32le msg 8))
  let entry ← indexLookup [.handshake] (u32le msg 8)
  let after ← Campaign2.read
  return ⟨before, observed, entry, after⟩

theorem responseLookupRead_bind {α : Type} (msg : List UInt8)
    (next : Option (IndexOwner × PeerId) → M α) :
    (responseLookupRead msg >>= fun out => next out.entry) =
      (indexLookup [.handshake] (u32le msg 8) >>= next) := by
  funext w
  change (((indexLookup [.handshake] (u32le msg 8)).run w >>= fun pair =>
    Except.ok (ResponseLookupRead.mk (Campaign2.snapshot w)
      (Campaign2.observeResult ((indexLookup [.handshake] (u32le msg 8)).run w)) pair.1
      (Campaign2.snapshot pair.2), pair.2)) >>= fun out => next out.1.entry out.2) =
      ((indexLookup [.handshake] (u32le msg 8)).run w >>= fun out => next out.1 out.2)
  cases hl : (indexLookup [.handshake] (u32le msg 8)).run w <;> rfl

/-- Original prefix through the read-lock state check. Invalid paths retain
their original reference put and return no candidate. -/
def responseLookupPrefix (msg : List UInt8) : M (Option ResponseLookupCut) := do
  let identity := (← getDev).staticIdentity
  if ← branch .crespNoIdentity !identity.hasIdentity then return none
  let lookup ← responseLookupRead msg
  let entry := lookup.entry
  if ← branch .crespNoHandshake entry.isNone then return none
  let some (IndexOwner.handshake owner, pid) := entry |
    invariant "a keypair entry under the handshake mask"
  let p ← getPeer pid
  if ← branch .crespNotCreatedInitiation (p.handshakeState != HANDSHAKE_CREATED_INITIATION) then
    peerPut (some pid)
    return none
  return some ⟨⟨identity, owner, pid, p⟩, lookup⟩

def responseEntrySuffix (msg : List UInt8) (entry : Option ResponseLookupCut) :
    M (Option ResponseConsumed) := do
  match entry with
  | none => return none
  | some entry => responseConsumeTail msg entry.input

/-- Completeness, not just observation erasure: every successful consumption
passes through this actual lookup prefix and the original crypto/commit tail. -/
theorem responseConsume_lookup (msg : List UInt8) :
    (responseLookupPrefix msg >>= responseEntrySuffix msg) = responseConsume msg := by
  simp only [responseLookupPrefix, responseEntrySuffix, responseConsume, bind_assoc,
    pure_bind, bind_if, bind_option, invariant_bind]
  congr 1
  funext d
  congr 1
  funext absent
  cases absent <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc]
  all_goals try rfl
  rw [← responseLookupRead_bind]
  congr 1
  funext lookup
  congr 1
  funext missing
  cases missing <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc]
  all_goals try rfl
  cases entry : lookup.entry with
  | none => rfl
  | some pair =>
    rcases pair with ⟨owner, pid⟩
    cases owner with
    | keypair id => rfl
    | handshake owner =>
      simp only [bind_assoc, pure_bind]
      congr 1
      funext p
      congr 1
      funext wrong
      cases wrong <;> simp [responseEntrySuffix, bind_assoc]

def responseWithLookup (msg : List UInt8) : M (Option (ResponseLookupCut × ResponseConsumed)) := do
  let entry ← responseLookupPrefix msg
  match entry with
  | none => return none
  | some entry =>
    let consumed ← responseConsumeTail msg entry.input
    return consumed.map fun out => (entry, out)

theorem responseWithLookup_consume (msg : List UInt8) :
    (do let out ← responseWithLookup msg; pure (out.map Prod.snd)) = responseConsume msg := by
  rw [← responseConsume_lookup]
  simp only [responseWithLookup, bind_assoc]
  congr 1
  funext entry
  cases entry with
  | none => rfl
  | some entry =>
    simp only [responseEntrySuffix, bind_assoc, pure_bind]
    change (responseConsumeTail msg entry.input >>= fun consumed => pure ((consumed.map fun out => (entry, out)).map Prod.snd)) = responseConsumeTail msg entry.input
    simp [Option.map_map, Function.comp_def]

theorem responseWithLookup_erase (msg : List UInt8) :
    (do let out ← responseWithLookup msg; pure (out.map fun pair => pair.2.input.pid)) =
      consumeResponse msg := by
  rw [← responseConsume_erase, ← responseWithLookup_consume]
  simp only [bind_assoc, pure_bind, responsePeer, Option.map_map, Function.comp_def]

theorem responseLookupRead_facts (msg : List UInt8) (identity : StaticIdentity) :
    Ensures (responseLookupRead msg)
      (fun w => w.k.wg.map Device.staticIdentity = some identity)
      (fun out w => out.before.wg.device.map Device.staticIdentity = some identity ∧
        out.after.wg.device = w.k.wg ∧ out.observed = .ok (out.entry, out.after)) := by
  intro w out final pre run
  change ((indexLookup [.handshake] (u32le msg 8)).run w >>= fun pair =>
    Except.ok (ResponseLookupRead.mk (Campaign2.snapshot w)
      (Campaign2.observeResult ((indexLookup [.handshake] (u32le msg 8)).run w)) pair.1
      (Campaign2.snapshot pair.2), pair.2)) = .ok (out, final) at run
  cases hl : (indexLookup [.handshake] (u32le msg 8)).run w with
  | error err => rw [hl] at run; cases run
  | ok pair =>
    rcases pair with ⟨entry, after⟩
    rw [hl] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    exact ⟨pre, rfl, rfl⟩

theorem responseLookupPrefix_facts (msg : List UInt8) :
    Ensures (responseLookupPrefix msg) (fun _ => True)
      (fun out _ => ∀ cut, out = some cut → ResponseLookupFacts cut) := by
  rw [ensures_iff]
  have hl := fun identity => (ensures_iff _ _ _).mp (responseLookupRead_facts msg identity)
  have hp (pid : PeerId) : ⦃fun _ => ⌜True⌝⦄ peerPut (some pid) ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro w x final pre run
    trivial
  mvcgen [responseLookupPrefix, getDev, getK, getPeer, branch, invariant, hl, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [ResponseLookupFacts]
  all_goals grind

theorem responseWithLookup_facts (msg : List UInt8) :
    Ensures (responseWithLookup msg) (fun _ => True)
      (fun result w => ∀ cut, result = some cut →
        ResponseLookupFacts cut.1 ∧ cut.2.input = cut.1.input ∧
        cut.2.committed = Campaign2.snapshot w ∧ ResponseConsumedFacts msg cut.2) := by
  intro w result final pre run
  simp only [responseWithLookup, StateT.run_bind] at run
  cases hp : (responseLookupPrefix msg).run w with
  | error err => rw [hp] at run; cases run
  | ok pair =>
    rcases pair with ⟨entry, after⟩
    rw [hp] at run
    cases entry with
    | none =>
      change Except.ok (none, after) = Except.ok (result, final) at run
      cases run
      simp
    | some entry =>
      have facts := responseLookupPrefix_facts msg w (some entry) after trivial hp entry rfl
      change ((responseConsumeTail msg entry.input).run after >>= fun out =>
        Except.ok (out.1.map (fun consumed => (entry, consumed)), out.2)) = .ok (result, final) at run
      cases ht : (responseConsumeTail msg entry.input).run after with
      | error err => rw [ht] at run; cases run
      | ok pair =>
        rcases pair with ⟨consumed, finish⟩
        rw [ht] at run
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
        cases consumed with
        | none => simp
        | some consumed =>
          have tail := responseConsumeTail_facts msg entry.input facts.2.2.2.2.1
            facts.2.2.2.2.2 after (some consumed) finish trivial ht consumed rfl
          intro cut same
          cases same
          exact ⟨facts, tail⟩

end Leanux.Proofs.WG.Roaming
