import Leanux.Proofs.WG.Roaming.ResponseCallSource
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem responsePacketPrefix_facts (msg : List UInt8) (src : SkbSource) (underLoad : Bool) :
    Campaign2.Ensures (responsePacketPrefix msg src underLoad) (fun _ => True)
      (fun result s => ∀ cut, result = some cut →
        cut.beforeSetter = s ∧ ResponseCallFacts msg cut) := by
  have bindRun {α β : Type} (a : WG.M α) (f : α → WG.M β)
      (g : WGWorld) (ambient : Ambient) :
      (((a >>= f).run g).run ambient) =
        (((a.run g).run ambient) >>= fun ((x, current), middle) =>
          ((f x).run current).run middle) := rfl
  have branchRun (site : Decision) (value : Bool) (g : WGWorld) (ambient : Ambient) :
      (((branch site value : WG.M Bool).run g).run ambient) =
        .ok ((value, g), {ambient with steps := ambient.steps.push {
          decision := site, outcome := value, netRx := ambient.netRxSection}}) := rfl
  have pureRun {α : Type} (x : α) (g : WGWorld) (ambient : Ambient) :
      (((pure x : WG.M α).run g).run ambient) = .ok ((x,g),ambient) := rfl
  have okBind {α β : Type} (x : α) (f : α → Except Stop β) :
      (Except.ok x >>= f) = f x := rfl
  have macEq (a b : MacState) : (a == b) = true ↔ a = b := by
    cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h
  have accepted (loaded : Bool) (mac : MacState)
      (valid : (loaded = true ∧ mac = .withCookie) ∨ (loaded = false ∧ mac = .noCookie)) :
      Campaign2.Ensures (do
        let consumed ← responseWithLookup msg
        if ← branch .hsRespNoPeer consumed.isNone then return none
        let some pair := consumed | invariant "unreachable"
        return some ⟨loaded, mac, pair.1, pair.2, ← Campaign2.read⟩ : WG.M (Option ResponseCallCut))
        (fun _ => True) (fun result s => ∀ cut, result = some cut →
          cut.beforeSetter = s ∧ ResponseCallFacts msg cut) := by
    intro g ambient result final after _ run
    rw [bindRun] at run
    cases consumedRun : ((responseWithLookup msg).run g).run ambient with
    | error stop => rw [consumedRun] at run; cases run
    | ok pair =>
      rcases pair with ⟨⟨consumed, current⟩, middle⟩
      rw [consumedRun] at run
      cases consumed with
      | none =>
        simp only [okBind, bindRun, branchRun, Option.isNone_none, ite_true, pureRun] at run
        cases run
        simp
      | some pair =>
        have facts := responseWithLookup_facts msg g ambient (some pair) current middle trivial consumedRun pair rfl
        simp only [okBind, bindRun, branchRun, Option.isNone_some, Bool.false_eq_true, ite_false] at run
        let logged := {middle with steps := middle.steps.push {decision := .hsRespNoPeer, outcome := false, netRx := middle.netRxSection}}
        change Except.ok ((some ⟨loaded, mac, pair.1, pair.2, Campaign2.snapshot current logged⟩,
          current), logged) = Except.ok ((result, final), after) at run
        have equal := Prod.mk.inj (Except.ok.inj run)
        rw [← (Prod.mk.inj equal.1).1, ← (Prod.mk.inj equal.1).2, ← equal.2]
        intro cut same
        cases same
        exact ⟨rfl, valid, facts.1, facts.2.1, facts.2.2.2,
          (congrArg (fun s : Campaign2.Snapshot => s.wg.device) facts.2.2.1).symm⟩
  intro g ambient result final after _ run
  unfold responsePacketPrefix at run
  rw [bindRun] at run
  cases cookieRun : ((cookieValidatePacket msg src underLoad).run g).run ambient with
  | error stop => rw [cookieRun] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨mac, current⟩, middle⟩
    rw [cookieRun] at run
    simp only [okBind] at run
    cases underLoad <;> cases mac
    all_goals simp only [WG.andM, WG.orM, bindRun, branchRun, pureRun, okBind,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, macEq, reduceCtorEq, ↓reduceIte] at run
    all_goals try { cases run; simp }
    case false.noCookie =>
      exact accepted false .noCookie (Or.inr ⟨rfl,rfl⟩) current _ result final after trivial run
    case true.withCookie =>
      exact accepted true .withCookie (Or.inl ⟨rfl,rfl⟩) current _ result final after trivial run
    case true.noCookie =>
      generalize sentRun : ((sendHandshakeCookie msg src).run current).run _ = sent at run
      cases sent with
      | error stop => cases run
      | ok pair => cases run; simp

theorem responseCallPrefix_facts (msg : List UInt8) (src : SkbSource) :
    Campaign2.Ensures (responseCallPrefix msg src) (fun _ => True)
      (fun result s => ∀ cut, result = some cut →
        cut.beforeSetter = s ∧ ResponseCallFacts msg cut) := by
  intro g ambient result final after _ run
  let logged := {ambient with steps := ambient.steps.push {decision := .hsCookie, outcome := false, netRx := ambient.netRxSection}}
  change (((responseLoad.run g).run logged) >>= fun ((loaded, current), middle) =>
    ((responsePacketPrefix msg src loaded).run current).run middle) = _ at run
  cases loadRun : (responseLoad.run g).run logged with
  | error stop => rw [loadRun] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨loaded, current⟩, middle⟩
    rw [loadRun] at run
    exact responsePacketPrefix_facts msg src loaded current middle result final after trivial run

theorem observedResponseHandshake_facts (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    Campaign2.Ensures (observedResponseHandshake msg src) (fun _ => True)
      (fun observed _ => ResponseCallObservation msg observed) := by
  intro g ambient observed final after _ run
  rw [observedResponseHandshake_source msg src kind] at run
  change (((responseCallPrefix msg src).run g).run ambient >>= fun ((candidate, atCut), cutAmbient) =>
    ((responseCallSuffix msg src candidate).run atCut).run cutAmbient >>= fun ((_, finish), ending) =>
      Except.ok ((Except.ok (candidate, Campaign2.snapshot atCut cutAmbient), finish), ending)) = _ at run
  cases prefixRun : ((responseCallPrefix msg src).run g).run ambient with
  | error stop => rw [prefixRun] at run; cases run
  | ok pair =>
    rcases pair with ⟨⟨candidate, atCut⟩, cutAmbient⟩
    rw [prefixRun] at run
    change (((responseCallSuffix msg src candidate).run atCut).run cutAmbient >>= fun ((_, finish), ending) =>
      Except.ok ((Except.ok (candidate, Campaign2.snapshot atCut cutAmbient), finish), ending)) = _ at run
    cases suffixRun : ((responseCallSuffix msg src candidate).run atCut).run cutAmbient with
    | error stop => rw [suffixRun] at run; cases run
    | ok pair =>
      rcases pair with ⟨⟨value, finish⟩, ending⟩
      rw [suffixRun] at run
      cases run
      exact ⟨candidate, Campaign2.snapshot atCut cutAmbient, rfl,
        responseCallPrefix_facts msg src g ambient candidate atCut cutAmbient trivial prefixRun⟩

end Leanux.Proofs.WG.Roaming
