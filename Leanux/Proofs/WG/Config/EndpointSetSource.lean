import Leanux.Proofs.WG.Config.EndpointSetModel
import Leanux.Proofs.WG.Config.ScalarGetterSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do

theorem endpointAnd_returns (a b : WG.M Bool) (x y : Bool) (P : WGWorld → Prop)
    (ha : Returns a P (fun v g => v = x ∧ P g))
    (hb : Returns b P (fun v g => v = y ∧ P g)) :
    Returns (WG.andM a b) P (fun v g => v = (x && y) ∧ P g) := by
  unfold WG.andM
  refine returns_bind _ _ ha ?_
  intro v g ambient pre
  obtain ⟨hv, hp⟩ := pre
  subst v
  cases x with
  | false => exact ⟨false, g, ambient, rfl, rfl, hp⟩
  | true => simpa using hb g ambient hp

/-- The original comparison returns its full effective predicate and preserves
the native state. This is a result contract, not merely a projection frame. -/
theorem endpointEq_returns_exact (a : Endpoint) (b : Option Endpoint) (P : WGWorld → Prop) :
    Returns (endpointEq a b) P (fun v g => v = endpointSame a b ∧ P g) := by
  have branchR (site : Decision) (value : Bool) :
      Returns (branch site value : WG.M Bool) P (fun v g => v = value ∧ P g) :=
    (returns_iff _ _ _).mpr (branch_state_returns P site value)
  let family := b.map (·.family) |>.getD 0
  let field (f : Endpoint → Nat) := b.any fun e => f e == f a
  let v4 := a.family == AF_INET && (family == AF_INET && (field (·.port) &&
    (field (·.addr) && (field (·.src) && field (·.srcIf)))))
  let v6 := a.family == AF_INET6 && (family == AF_INET6 && (field (·.port) &&
    (field (·.addr) && (field (·.scope) && field (·.src)))))
  have model : endpointSame a b = (v4 || v6 || (a.family == 0 && family == 0)) := by
    simp only [endpointSame, v4, v6, field, family, Bool.and_assoc]
  unfold endpointEq
  refine returns_bind _ _ (endpointAnd_returns _ _ _ _ P (branchR _ _)
    (endpointAnd_returns _ _ _ _ P (branchR _ _)
      (endpointAnd_returns _ _ _ _ P (branchR _ _)
        (endpointAnd_returns _ _ _ _ P (branchR _ _)
          (endpointAnd_returns _ _ _ _ P (branchR _ _) (branchR _ _)))))) ?_
  intro first g ambient pre
  obtain ⟨equal, hp⟩ := pre
  have hfirst : first = v4 := equal
  subst first
  change ∃ ret final after, ((if v4 then pure true else _ : WG.M Bool).run g).run ambient = .ok ((ret, final), after) ∧ ret = endpointSame a b ∧ P final
  cases h4 : v4 with
  | true =>
    refine ⟨true, g, ambient, rfl, ?_, hp⟩
    simp only [model, h4, Bool.true_or]
  | false =>
    have second := endpointAnd_returns _ _ _ _ P (branchR .eqA6 (a.family == AF_INET6))
      (endpointAnd_returns _ _ _ _ P (branchR .eqB6 (family == AF_INET6))
        (endpointAnd_returns _ _ _ _ P (branchR .eqPort6 (field (·.port)))
          (endpointAnd_returns _ _ _ _ P (branchR .eqAddr6 (field (·.addr)))
            (endpointAnd_returns _ _ _ _ P (branchR .eqScope6 (field (·.scope))) (branchR .eqSrc6 (field (·.src)))))))
    refine (returns_bind _ _ second ?_) g ambient hp
    intro value middle next pre
    obtain ⟨equal, framed⟩ := pre
    subst value
    change ∃ ret final after, ((if v6 then pure true else _ : WG.M Bool).run middle).run next = .ok ((ret, final), after) ∧ ret = endpointSame a b ∧ P final
    cases h6 : v6 with
    | true => exact ⟨true, middle, next, rfl, by simp [model, h6], framed⟩
    | false =>
      obtain ⟨last, final, rest, lastRun, lastValue, lastFrame⟩ :=
        (endpointAnd_returns _ _ _ _ P (branchR .eqANone (a.family == 0))
          (branchR .eqBNone (family == 0))) middle next framed
      exact ⟨last, final, rest, lastRun, by simpa [model, h4, h6] using lastValue, lastFrame⟩

/-- Exact optional reset store from the original cache-reset leaf. -/
theorem endpointReset_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (dstCacheReset pid)
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => ∃ reset : Option UInt64,
        g.dev = some (match reset with
          | none => d
          | some ts => withPeer d pid {p with dstCache := {p.dstCache with resetTs := ts}}) ∧
        readbackFrame g sock fixtures) := by
  intro g ambient result final after pre run
  obtain ⟨device, frame⟩ := pre
  have hiddenLift : (hiddenJiffies .dstCacheResetTs : WG.M UInt64) =
      StateT.lift (AmbientM.hiddenJiffies .dstCacheResetTs) := rfl
  cases mode : ambient.armRecords && g.dstCacheRecords with
  | false =>
    have disabled : ambient.armRecords = false ∨ g.dstCacheRecords = false := by
      cases arm : ambient.armRecords with
      | false => exact Or.inl rfl
      | true => exact Or.inr (by simpa [arm] using mode)
    simp [dstCacheReset, getAmbient, disabled] at run
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
    exact ⟨none, device, frame⟩
  | true =>
    have modes : ambient.armRecords = true ∧ g.dstCacheRecords = true := by simpa using mode
    cases draw : (AmbientM.hiddenJiffies .dstCacheResetTs).run ambient with
    | error stop =>
      simp [dstCacheReset, getAmbient, modes.1, modes.2, hiddenLift, draw] at run
      change (Except.error stop : Except Stop _) = .ok ((result, final), after) at run
      cases run
    | ok output =>
      obtain ⟨reset, next⟩ := output
      simp [dstCacheReset, getAmbient, modes.1, modes.2, hiddenLift, draw,
        getPeer, getDev, setPeer, modifyDev, device, resident] at run
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
      exact ⟨some reset, rfl, frame⟩

/-- Normal effects preserve ordered writes. The no-change comparison performs
no reset; a changed endpoint may consume an actual reset timestamp. -/
theorem setPeerEndpoint_exact (pid : PeerId) (e : Endpoint) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (valid : e.family = AF_INET ∨ e.family = AF_INET6)
    (sock : NlSock) (fixtures : FixtureDevices) :
    Ensures (setPeerEndpoint pid e)
      (fun g => g.dev = some d ∧ readbackFrame g sock fixtures)
      (fun _ g => ∃ reset : Option UInt64,
        g.dev = some (endpointStores d pid p e reset) ∧ readbackFrame g sock fixtures ∧
        (endpointSame e p.endpoint = true → reset = none)) := by
  let P : WGWorld → Prop := fun g => g.dev = some d ∧ readbackFrame g sock fixtures
  let Q : Unit → WGWorld → Prop := fun _ g => ∃ reset : Option UInt64,
    g.dev = some (endpointStores d pid p e reset) ∧ readbackFrame g sock fixtures ∧
    (endpointSame e p.endpoint = true → reset = none)
  have read : Ensures (getPeer pid) P (fun q g => q = p ∧ P g) := by
    intro g ambient result final after pre run
    simp [getPeer, getDev, pre.1, resident] at run
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
    exact ⟨rfl, pre⟩
  have branchNext (site : Decision) (value : Bool) (f : Bool → WG.M Unit)
      (body : Ensures (f value) P Q) : Ensures ((branch site value : WG.M Bool) >>= f) P Q := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (branch_state_spec P site value)) ?_
    intro ret g ambient result final after pre run
    obtain ⟨rfl, hp⟩ := pre
    exact body g ambient result final after hp run
  have write (different : endpointSame e p.endpoint = false) :
      Ensures (do setPeer pid { (← getPeer pid) with endpoint := some e }; dstCacheReset pid) P Q := by
    refine ensures_bind _ _ read ?_
    intro q g ambient result final after pre run
    obtain ⟨hq, device, frame⟩ := pre
    subst q
    let written := {p with endpoint := some e}
    let changed := withPeer d pid written
    have initial : ((do setPeer pid written; dstCacheReset pid : WG.M Unit).run g).run ambient =
        ((dstCacheReset pid).run {g with dev := some changed}).run ambient := by
      simp [setPeer, modifyDev, device, changed, withPeer]
    rw [initial] at run
    obtain ⟨reset, effect, framed⟩ := endpointReset_exact pid changed written
      (by simp [changed, withPeer]) sock fixtures {g with dev := some changed}
      ambient result final after ⟨rfl, frame⟩ run
    refine ⟨reset, ?_, framed, by simp [different]⟩
    cases reset <;> simpa [endpointStores, different, changed, written] using effect
  have family (different : endpointSame e p.endpoint = false) :
      Ensures (do
        if ← branch .setEndpointV4 (e.family == AF_INET) then
          setPeer pid { (← getPeer pid) with endpoint := some e }; dstCacheReset pid
        else if ← branch .setEndpointV6 (e.family == AF_INET6) then
          setPeer pid { (← getPeer pid) with endpoint := some e }; dstCacheReset pid) P Q := by
    refine branchNext _ _ _ ?_
    rcases valid with v4 | v6
    · simpa [v4] using write different
    · simp only [v6, AF_INET, AF_INET6, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
      refine branchNext _ _ _ ?_
      exact write different
  unfold setPeerEndpoint
  simp only [requireNotPending, pure_bind]
  refine ensures_bind _ _ read ?_
  intro q g ambient result final after pre run
  obtain ⟨hq, hp⟩ := pre
  subst q
  have compare : Ensures (endpointEq e p.endpoint) P
      (fun equal g => equal = endpointSame e p.endpoint ∧ P g) := by
    intro initial a value out rest before executed
    obtain ⟨actual, endState, endAmbient, closed, facts⟩ := endpointEq_returns_exact e p.endpoint P initial a before
    rw [closed] at executed
    cases executed
    exact facts
  have body : Ensures (do
      if ← branch .setEndpointEq (← endpointEq e p.endpoint) then return
      if ← branch .setEndpointV4 (e.family == AF_INET) then
        setPeer pid { (← getPeer pid) with endpoint := some e }; dstCacheReset pid
      else if ← branch .setEndpointV6 (e.family == AF_INET6) then
        setPeer pid { (← getPeer pid) with endpoint := some e }; dstCacheReset pid) P Q := by
    refine ensures_bind _ _ compare ?_
    intro equal initial a value out rest before executed
    obtain ⟨rfl, hp⟩ := before
    have restSpec : Ensures (do
        if ← branch .setEndpointEq (endpointSame e p.endpoint) then return
        if ← branch .setEndpointV4 (e.family == AF_INET) then
          setPeer pid { (← getPeer pid) with endpoint := some e }; dstCacheReset pid
        else if ← branch .setEndpointV6 (e.family == AF_INET6) then
          setPeer pid { (← getPeer pid) with endpoint := some e }; dstCacheReset pid) P Q := by
      refine branchNext _ _ _ ?_
      cases same : endpointSame e p.endpoint with
      | false => exact family same
      | true =>
        intro entry before value final after pre executed
        cases executed
        exact ⟨none, by simpa [endpointStores, same] using pre.1, pre.2, fun _ => rfl⟩
    exact restSpec initial a value out rest hp executed
  exact body g ambient result final after hp run

end Leanux.Proofs.WG.Config
