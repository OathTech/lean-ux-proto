import Leanux.Proofs.WG.Roaming.ResponseConsumeSource
import Leanux.Proofs.WG.Config.BranchSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The inspection and the original lookup start at exactly the same state.
The original lookup executes once on the continuing path. -/
def responseLookupRead (msg : List UInt8) : WG.M ResponseLookupRead := do
  let before ← Campaign2.read
  let observed ← Campaign2.inspect (indexLookup [.handshake] (u32le msg 8))
  let entry ← indexLookup [.handshake] (u32le msg 8)
  let after ← Campaign2.read
  return ⟨before, observed, entry, after⟩

theorem responseLookupRead_bind {α : Type} (msg : List UInt8)
    (next : Option (IndexOwner × PeerId) → WG.M α) :
    (responseLookupRead msg >>= fun out => next out.entry) =
      (indexLookup [.handshake] (u32le msg 8) >>= next) := by
  funext g ambient
  change ((((indexLookup [.handshake] (u32le msg 8)).run g).run ambient >>= fun ((entry, current), after) =>
    Except.ok ((ResponseLookupRead.mk (Campaign2.snapshot g ambient)
      (Campaign2.observeResult (((indexLookup [.handshake] (u32le msg 8)).run g).run ambient)) entry
      (Campaign2.snapshot current after), current), after)) >>= fun ((out, current), after) =>
        ((next out.entry).run current).run after) =
    (((indexLookup [.handshake] (u32le msg 8)).run g).run ambient >>= fun ((entry, current), after) =>
      ((next entry).run current).run after)
  cases lookup : ((indexLookup [.handshake] (u32le msg 8)).run g).run ambient with
  | error err => rfl
  | ok pair => rcases pair with ⟨⟨entry, current⟩, after⟩; rfl

/-- Original prefix through the read-lock state check. Invalid paths retain
their original reference put and return no candidate. -/
def responseLookupPrefix (msg : List UInt8) : WG.M (Option ResponseLookupCut) := do
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
    WG.M (Option ResponseConsumed) := do
  match entry with
  | none => return none
  | some entry => responseConsumeTail msg entry.input

/-- Completeness, not just observation erasure: every successful consumption
passes through this actual lookup prefix and the original crypto/commit tail. -/
theorem responseConsume_lookup (msg : List UInt8) :
    (responseLookupPrefix msg >>= responseEntrySuffix msg) = responseConsume msg := by
  simp only [responseLookupPrefix, responseConsume, bind_assoc]
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
  cases missing <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind]
  all_goals try rfl
  cases entry : lookup.entry with
  | none => rfl
  | some pair =>
    rcases pair with ⟨owner, pid⟩
    cases owner with
    | keypair id => rfl
    | handshake owner =>
      simp only [bind_assoc]
      congr 1
      funext p
      congr 1
      funext wrong
      cases wrong <;> simp [responseEntrySuffix]

def responseWithLookup (msg : List UInt8) : WG.M (Option (ResponseLookupCut × ResponseConsumed)) := do
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
    Campaign2.Ensures (responseLookupRead msg)
      (fun s => s.wg.device.map Device.staticIdentity = some identity)
      (fun out s => out.before.wg.device.map Device.staticIdentity = some identity ∧
        out.after.wg.device = s.wg.device ∧ out.observed = .ok (out.entry, out.after)) := by
  intro g ambient out final after pre run
  change (((indexLookup [.handshake] (u32le msg 8)).run g).run ambient >>= fun ((entry, current), last) =>
    Except.ok ((ResponseLookupRead.mk (Campaign2.snapshot g ambient)
      (Campaign2.observeResult (((indexLookup [.handshake] (u32le msg 8)).run g).run ambient)) entry
      (Campaign2.snapshot current last), current), last)) = .ok ((out, final), after) at run
  cases lookup : ((indexLookup [.handshake] (u32le msg 8)).run g).run ambient with
  | error err => rw [lookup] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨entry, current⟩, last⟩
    rw [lookup] at run
    cases run
    exact ⟨pre, rfl, rfl⟩

theorem responseLookupPrefix_facts (msg : List UInt8) :
    Campaign2.Ensures (responseLookupPrefix msg) (fun _ => True)
      (fun out _ => ∀ cut, out = some cut → ResponseLookupFacts cut) := by
  let Q : Option ResponseLookupCut → WGWorld → Prop := fun out _ =>
    ∀ cut, out = some cut → ResponseLookupFacts cut
  change Ensures _ (fun _ => True) Q
  have hnone (P : WGWorld → Prop) : Ensures (pure none : WG.M (Option ResponseLookupCut)) P Q := by
    intro g ambient result final after _ run
    cases run
    intro cut impossible
    cases impossible
  have hfail (pid : PeerId) (P : WGWorld → Prop) :
      Ensures (do peerPut (some pid); pure none : WG.M _) P Q := by
    refine ensures_bind (Q := fun _ _ => True) _ _ ?_ (fun _ => hnone _)
    intro _ _ _ _ _ _ _
    trivial
  have hbranch {α : Type} (site : Decision) (value : Bool) (next : Bool → WG.M α)
      (P : WGWorld → Prop) (R : α → WGWorld → Prop) (hnext : Ensures (next value) P R) :
      Ensures ((branch site value : WG.M Bool) >>= next) P R := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (Config.branch_state_spec P site value)) ?_
    intro found g ambient result final after pre run
    rcases pre with ⟨rfl, pre⟩
    exact hnext g ambient result final after pre run
  have hdev : Ensures getDev (fun _ => True) (fun d g => g.dev = some d) := by
    intro g ambient d final after _ run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some found => simp [getDev, device] at run; rcases run with ⟨⟨rfl, rfl⟩, rfl⟩; exact device
  unfold responseLookupPrefix
  refine ensures_bind _ _ hdev ?_
  intro d
  refine hbranch _ _ _ _ _ ?_
  cases identity : d.staticIdentity.hasIdentity with
  | false => simpa [identity] using hnone (fun g => g.dev = some d)
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine ensures_bind (Q := fun out g =>
      out.before.wg.device.map Device.staticIdentity = some d.staticIdentity ∧
      out.after.wg.device = g.dev ∧ out.observed = .ok (out.entry, out.after)) _ _ ?_ ?_
    · intro g ambient out final after device run
      exact responseLookupRead_facts msg d.staticIdentity g ambient out final after
        (by change g.dev.map Device.staticIdentity = _; simp [device]) run
    · intro lookup
      refine hbranch _ _ _ _ _ ?_
      cases entry : lookup.entry with
      | none => simp only [Option.isNone_none, ↓reduceIte]; exact hnone _
      | some pair =>
        rcases pair with ⟨owner, pid⟩
        cases owner with
        | keypair id =>
          simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
          intro g ambient result final after _ run
          simp [invariant, AmbientM.invariant] at run
          cases run
        | handshake owner =>
          simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
          refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid _)) ?_
          intro p
          refine hbranch _ _ _ _ _ ?_
          by_cases created : p.handshakeState = HANDSHAKE_CREATED_INITIATION
          · simp only [created, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
            intro g ambient result final after pre run
            cases run
            intro cut same
            cases same
            rcases pre with ⟨⟨initial, device, observed⟩, resident⟩
            exact ⟨entry, by simpa [entry] using observed, initial,
              by simpa [device, peerAt] using resident, identity, created⟩
          · simp only [bne, beq_eq_false_iff_ne.mpr created, Bool.not_false, ↓reduceIte]
            exact hfail pid _

theorem responseWithLookup_facts (msg : List UInt8) :
    Campaign2.Ensures (responseWithLookup msg) (fun _ => True)
      (fun result s => ∀ cut, result = some cut →
        ResponseLookupFacts cut.1 ∧ cut.2.input = cut.1.input ∧
        cut.2.committed = s ∧ ResponseConsumedFacts msg cut.2) := by
  intro g ambient result final after _ run
  dsimp only [responseWithLookup, StateT.run, StateT.bind, StateT.pure,
    Bind.bind, Pure.pure, Except.bind, Except.pure] at run
  cases firstRun : ((responseLookupPrefix msg).run g).run ambient with
  | error err => simp only [StateT.run] at firstRun; rw [firstRun] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨entry, current⟩, middle⟩
    simp only [StateT.run] at firstRun
    rw [firstRun] at run
    cases entry with
    | none => cases run; simp
    | some entry =>
      have facts := responseLookupPrefix_facts msg g ambient (some entry) current middle trivial firstRun entry rfl
      change (((responseConsumeTail msg entry.input).run current).run middle >>= fun ((consumed, last), ending) =>
        Except.ok ((consumed.map (fun value => (entry, value)), last), ending)) = _ at run
      cases tailRun : ((responseConsumeTail msg entry.input).run current).run middle with
      | error err => rw [tailRun] at run; cases run
      | ok pair =>
        rcases pair with ⟨⟨consumed, last⟩, ending⟩
        rw [tailRun] at run
        cases run
        cases consumed with
        | none => simp
        | some consumed =>
          have tail := responseConsumeTail_facts msg entry.input facts.2.2.2.2.1
            facts.2.2.2.2.2 current middle (some consumed) final after trivial tailRun consumed rfl
          intro cut same
          cases same
          exact ⟨facts, tail⟩

end Leanux.Proofs.WG.Roaming
