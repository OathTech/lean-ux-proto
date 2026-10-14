import Leanux.Proofs.WG.Configuration.PeerTailRouting

/-! Address shape propagates through the original parser. Malformed entries
remain legal parsed constructors; family, length and CIDR guards belong to the
original configuration call, not to this shape predicate. Private-source pins and
a literal suffix cut with an rfl equation preserve the public parser exactly. -/
namespace Leanux.Proofs.WG.Configuration
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.WG.AllowedIps
set_option maxHeartbeats 1000000

def PeerEntryAddressShape : PeerEntry → Prop
  | .malformed => True
  | .attrs a => PeerAddressShape a

def DeviceAddressShape (a : DeviceAttrs) : Prop :=
  ∀ p, PeerEntry.attrs p ∈ a.peers.getD [] → PeerAddressShape p

def OperationAddressShape : Operation → Prop
  | .wgSet a => DeviceAddressShape a
  | _ => True

def TraceAddressShape (trace : Trace) : Prop :=
  ∀ op ∈ trace.ops, OperationAddressShape op

/-- These wrappers refer to the actual private source parsers. -/
def parsePeer := pinned_const _private.Leanux.Runner.«0».Leanux.Runner.parsePeer
def parseConfig := pinned_const _private.Leanux.Runner.«0».Leanux.Runner.parseConfig
def parseOperation := pinned_const _private.Leanux.Runner.«0».Leanux.Runner.parseOperation

private def Good {ε α : Type} (a : Except ε α) (P : α → Prop) : Prop := ∀ x, a = .ok x → P x

-- Introduce actual continuation binders without unfolding the semantic predicate.
elab "parser_intro" : tactic => do
  unless (← Lean.Elab.Tactic.getMainTarget).isForall do
    Lean.throwError "expected an explicit continuation binder"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro x))

private theorem good_pure {ε α : Type} {P : α → Prop} (x : α) (hx : P x) : Good (pure x : Except ε α) P := by
  intro y hy
  cases hy
  exact hx

private theorem good_throw {ε α : Type} {P : α → Prop} (e : ε) : Good (throw e : Except ε α) P := by
  intro x hx
  cases hx

private theorem good_bind {ε α β : Type} {P : α → Prop} {Q : β → Prop} (a : Except ε α) (f : α → Except ε β)
    (ha : Good a P) (hf : ∀ x, P x → Good (f x) Q) : Good (a >>= f) Q := by
  intro y hy
  cases h : a with
  | error e => simp [h, bind, Except.bind] at hy
  | ok x => exact hf x (ha x h) y (by simpa [h, bind, Except.bind] using hy)

private theorem good_map {ε α β : Type} {P : α → Prop} {Q : β → Prop}
    (f : α → β) (a : Except ε α) (ha : Good a P) (hf : ∀ x, P x → Q (f x)) :
    Good (f <$> a) Q := by
  intro y hy
  change Except.map f a = .ok y at hy
  cases h : a with
  | error e => simp [h, Except.map] at hy
  | ok x =>
    have he : f x = y := by simpa [h, Except.map] using hy
    exact he ▸ hf x (ha x h)

private theorem good_if {ε α : Type} {P : α → Prop} (c : Prop) [Decidable c]
    (a b : Except ε α) (ha : Good a P) (hb : Good b P) : Good (if c then a else b) P := by
  split <;> assumption

elab "parser_trace_goal" : tactic => do
  unless (← Lean.Elab.Tactic.getMainTarget).headBeta.isAppOf ``TraceAddressShape do
    Lean.throwError "expected the final trace predicate"

elab "parser_good_goal" : tactic => do
  unless (← Lean.Elab.Tactic.getMainTarget).isAppOf ``Good do
    Lean.throwError "expected an unreduced parser contract"

private theorem good_abort_bind {ε α β : Type} {P : β → Prop}
    (e : ε) (f : α → Except ε β) : Good ((throw e : Except ε α) >>= f) P := by
  intro x hx
  cases hx

private theorem good_bind_any {ε α β : Type} {Q : β → Prop} (a : Except ε α) (f : α → Except ε β)
    (hf : ∀ x, Good (f x) Q) : Good (a >>= f) Q :=
  good_bind a f (fun _ _ => True.intro) (fun x _ => hf x)

private theorem good_mapIdx {ε α β : Type} {P : β → Prop} (f : Nat → α → Except ε β)
    (hf : ∀ i x, Good (f i x) P) (xs : List α) :
    Good (xs.mapIdxM f) (fun ys => ∀ y ∈ ys, P y) := by
  have go (xs : List α) (acc : Array β) (ha : ∀ y ∈ acc, P y) :
      Good (List.mapIdxM.go f xs acc) (fun ys => ∀ y ∈ ys, P y) := by
    induction xs generalizing acc with
    | nil =>
      apply good_pure
      simpa using ha
    | cons x xs ih =>
      unfold List.mapIdxM.go
      with_reducible apply good_bind (f acc.size x) (fun y => List.mapIdxM.go f xs (acc.push y)) (hf acc.size x)
      intro y hy
      apply ih
      intro z hz
      rcases Array.mem_push.mp hz with hz | rfl
      · exact ha z hz
      · exact hy
  exact go xs #[] (by simp)

private theorem good_optionList {ε α β : Type} {P : β → Prop} (f : α → Except ε (List β))
    (hf : ∀ x, Good (f x) (fun ys => ∀ y ∈ ys, P y)) (o : Option α) :
    Good (o.mapM f) (fun ys => ∀ y ∈ ys.getD [], P y) := by
  cases o with
  | none => exact good_pure _ (by simp)
  | some x =>
    change Good (f x >>= fun ys => pure (some ys)) _
    with_reducible apply good_bind _ _ (hf x)
    intro ys hy
    exact good_pure _ hy

private theorem allowedIps_good (what : String) (a : Json) :
    Good (do
      let ips ← a.getArr?
      if ips.size > 32 then throw s!"{what}.allowed_ips: expected at most 32 entries"
      ips.toList.mapIdxM fun k ip => parseAllowedIp ip s!"{what}.allowed_ips[{k}]")
      (fun ips => ∀ entry ∈ ips, EntryAddressShape entry) := by
  apply good_bind_any
  intro ips
  split
  · exact good_throw _
  · exact good_mapIdx _ (fun _ _ => parseAllowedIp_shape _ _) _

theorem parsePeer_shape (j : Json) (i : Nat) (entry : PeerEntry)
    (hr : parsePeer j i = .ok entry) : PeerEntryAddressShape entry := by
  have ips (what : String) (o : Option Json) := good_optionList _ (allowedIps_good what) o
  unfold parseAllowedIp at ips
  have good : Good (parsePeer j i) PeerEntryAddressShape := by
    unfold parsePeer
    parser_unfold _private.Leanux.Runner.«0».Leanux.Runner.parsePeer
    repeat' first
      | with_reducible apply good_map _ _ (ips _ _)
      | with_reducible apply good_bind _ _ (ips _ _)
      | with_reducible exact good_abort_bind _ _
      | with_reducible exact good_throw _
      | with_reducible apply good_if
      | with_reducible apply good_bind_any
      | with_reducible exact good_throw _
      | with_reducible apply good_pure
      | parser_intro
      | (with_reducible split)
    all_goals simp_all [PeerEntryAddressShape, PeerAddressShape, EntryAddressShape]
    all_goals
      intro ip hi
      exact (show ∀ e ∈ _, EntryAddressShape e from by assumption) (.attrs ip) hi
  exact good entry hr

private theorem peers_good (p : Json) :
    Good (do
      let ps ← p.getArr?
      if ps.size > 16 then throw "config.peers: expected at most 16 peers"
      ps.toList.mapIdxM fun i peer => parsePeer peer i)
      (fun ps => ∀ entry ∈ ps, PeerEntryAddressShape entry) := by
  with_reducible apply good_bind_any
  intro ps
  split
  · exact good_throw _
  · exact good_mapIdx _ (fun i peer => parsePeer_shape peer i) _

theorem parseConfig_shape (j : Json) (attrs : DeviceAttrs)
    (hr : parseConfig j = .ok attrs) : DeviceAddressShape attrs := by
  have peers (o : Option Json) := good_optionList _ peers_good o
  unfold parsePeer at peers
  have good : Good (parseConfig j) DeviceAddressShape := by
    unfold parseConfig
    parser_unfold _private.Leanux.Runner.«0».Leanux.Runner.parseConfig
    repeat' first
      | with_reducible apply good_map _ _ (peers _)
      | with_reducible apply good_bind _ _ (peers _)
      | with_reducible exact good_abort_bind _ _
      | with_reducible exact good_throw _
      | with_reducible apply good_if
      | with_reducible apply good_bind_any
      | with_reducible exact good_throw _
      | with_reducible apply good_pure
      | parser_intro
      | (with_reducible split)
    all_goals
      intro p hp
      exact (show ∀ e ∈ _, PeerEntryAddressShape e from by assumption) (.attrs p) hp
  exact good attrs hr

theorem parseOperation_shape (j : Json) (prior : Array Operation) (op : Operation)
    (hr : parseOperation j prior = .ok op) : OperationAddressShape op := by
  have config (j : Json) : Good (parseConfig j) DeviceAddressShape := parseConfig_shape j
  unfold parseConfig at config
  have good : Good (parseOperation j prior) OperationAddressShape := by
    unfold parseOperation
    parser_unfold _private.Leanux.Runner.«0».Leanux.Runner.parseOperation
    repeat' first
      | with_reducible apply good_map _ _ (config _)
      | with_reducible apply good_bind _ _ (config _)
      | with_reducible exact good_abort_bind _ _
      | with_reducible exact good_throw _
      | with_reducible apply good_if
      | with_reducible apply good_bind_any
      | with_reducible exact good_throw _
      | with_reducible apply good_pure
      | parser_intro
      | (with_reducible split)
    all_goals try dsimp only [OperationAddressShape, DeviceAddressShape] at *
    all_goals first | trivial | assumption
  exact good op hr

private def StepShape (P : α → Prop) : ForInStep α → Prop
  | .done x | .yield x => P x

private theorem good_forIn {α β : Type} (xs : List α) (acc : β) (P : β → Prop)
    (body : α → β → Except String (ForInStep β)) (hi : P acc)
    (hb : ∀ x b, P b → Good (body x b) (StepShape P)) :
    Good (forIn xs acc body) P := by
  induction xs generalizing acc with
  | nil => exact good_pure _ hi
  | cons x xs ih =>
    rw [List.forIn_cons]
    with_reducible apply good_bind _ _ (hb x acc hi)
    intro step hs
    cases step with
    | done b => exact good_pure _ hs
    | yield b => exact ih b hs

private theorem good_array {α β : Type} (xs : Array α) (acc : β) (P : β → Prop)
    (body : α → β → Except String (ForInStep β)) (hi : P acc)
    (hb : ∀ x b, P b → Good (body x b) (StepShape P)) :
    Good (forIn xs acc body) P := by
  rw [← Array.forIn_toList]
  exact good_forIn _ _ _ _ hi hb

private def OpsShape (acc : Array Operation × Array Nat) : Prop :=
  ∀ op ∈ acc.1, OperationAddressShape op

private theorem good_ops_array (xs : Array Json)
    (body : Json → (Array Operation × Array Nat) → Except String (ForInStep (Array Operation × Array Nat)))
    (hb : ∀ x b, OpsShape b → Good (body x b) (StepShape OpsShape)) :
    Good (forIn xs (#[], #[]) body) OpsShape :=
  good_array xs (#[], #[]) OpsShape body (by simp [OpsShape]) hb

-- This literal loop is the operations accumulator inside the public parser.
private def parseOps (rawOps : Array Json) : Except String (Array Operation × Array Nat) := do
  let mut ops := #[]
  let mut pauses := #[]
  for j in rawOps do
    let obj ← j.getObj?
    let (j, pause) ← match obj.get? "pause_ms" with
      | some v => do
        let n ← v.getNat?
        if n < 1 || n > PAUSE_MS_MAX then throw "pause_ms outside 1..20"
        pure (Json.obj (obj.erase "pause_ms"), n)
      | none => pure (j, 0)
    ops := ops.push (← parseOperation j ops)
    pauses := pauses.push pause
  return (ops, pauses)

private theorem parseOps_good (rawOps : Array Json) : Good (parseOps rawOps) OpsShape := by
  have operation (j : Json) (prior : Array Operation) :
      Good (parseOperation j prior) OperationAddressShape := parseOperation_shape j prior
  unfold parseOps
  repeat' first
    | with_reducible apply good_map _ _ (good_ops_array _ _ ?_)
    | with_reducible apply good_bind _ _ (good_ops_array _ _ ?_)
    | with_reducible apply good_map _ _ (operation _ _)
    | with_reducible apply good_bind _ _ (operation _ _)
    | with_reducible exact good_abort_bind _ _
    | with_reducible exact good_throw _
    | with_reducible apply good_if
    | with_reducible apply good_bind_any
    | with_reducible apply good_pure
    | parser_intro
    | (with_reducible split)
  all_goals try dsimp only [StepShape, OpsShape] at *
  all_goals first
    | assumption
    | (intro op hm
       rcases Array.mem_push.mp hm with hm | rfl
       · exact (show ∀ op ∈ _, OperationAddressShape op from by assumption) op hm
       · assumption)

private theorem pair_eta (p : α × β) : (p.1, p.2) = p := by cases p; rfl


private abbrev source_field := pinned_const _private.Leanux.Runner.«0».Leanux.Runner.field
private abbrev source_fields := pinned_const _private.Leanux.Runner.«0».Leanux.Runner.fields
private abbrev source_natField := pinned_const _private.Leanux.Runner.«0».Leanux.Runner.natField
private abbrev source_parseHidden := pinned_const _private.Leanux.Runner.«0».Leanux.Runner.parseHidden
private abbrev source_hexBytes := pinned_const _private.Leanux.Runner.«0».Leanux.Runner.hexBytes
private abbrev source_bigEndian := pinned_const _private.Leanux.Runner.«0».Leanux.Runner.bigEndian

private def traceFinish (j : Json) (id : String) (ops : Array Operation) (pauses : Array Nat)
    (rlimit : Nat) (armRecords dstCacheRecords hasHidden hasSteer hasPlacement hasFixture
      hasArmed hasSeccompChild hasSeccompPrefill : Bool) : Except String Trace := do
  let hidden ← if hasHidden then some <$> source_parseHidden (← source_field j "hidden") ops.size else pure none
  let steer ← if hasSteer then (← (← source_field j "steer").getArr?).toList.mapM fun e => do
      let pair ← e.getArr?
      if pair.size != 2 then throw "steer: expected [site, value] entries"
      let label ← pair[0]!.getStr?
      let v ← pair[1]!.getStr?
      if v == "draw" then return (label, none)
      if v.length == 0 || v.length % 2 != 0 || v.length > 80 then throw "steer: value hex"
      return (label, some (← source_hexBytes pair[1]! v.length "steer"))
    else pure []
  let napiBeforePut ← if hasPlacement then
      (← (← source_field j "napi_irq_before_put").getArr?).toList.mapM fun b => b.getBool?
    else pure []
  if napiBeforePut.length > 8 then throw "napi_irq_before_put: more than 8 entries"
  -- L: "bare"; W8: "foreign-creator"; W4: {"routes": [...]}
  let (bare, foreign, routes) ← if hasFixture then do
      let f ← source_field j "net_fixture"
      match f.getStr? with
      | .ok "bare" => pure (true, false, [])
      | .ok "foreign-creator" => pure (false, true, [])
      | .ok _ => throw "net_fixture: expected \"bare\", \"foreign-creator\" or {\"routes\": [...]}"
      | .error _ => do
        -- W4: the fixture's routes into wg0 with an MTU (section 6)
        source_fields f ["routes"]
        let rs ← (← (← source_field f "routes").getArr?).toList.mapM fun r => do
          source_fields r ["family", "dst", "mtu"]
          let family ← (← source_field r "family").getNat?
          if family != 4 && family != 6 then throw "net_fixture.routes[].family: expected 4 or 6"
          let addr := source_bigEndian (← source_hexBytes (← source_field r "dst") (if family == 4 then 8 else 32) "net_fixture.routes[].dst")
          let mtu ← (← source_field r "mtu").getNat?
          if mtu < 68 || mtu > 65535 then throw "net_fixture.routes[].mtu: expected 68-65535"
          pure (family, addr, mtu)
        if rs.isEmpty || rs.length > 8 then throw "net_fixture.routes: expected 1-8 routes"
        pure (false, false, rs)
    else pure (false, false, [])
  let allocArmed ← if hasArmed then (← (← source_field j "alloc_armed").getArr?).toList.mapM fun e => do
      let label ← e.getStr?
      if !(AllocSite.all.any fun s => s.info.label == label && s.info.count != .cut) then
        throw s!"alloc_armed: {label} is not a consumed allocation site"
      pure label
    else pure []
  if hasArmed && !hasHidden then throw "alloc_armed: an armed run carries its records"
  let seccompChild ← if hasSeccompChild then (← source_field j "seccomp_child").getBool? else pure false
  let seccompPrefill ← if hasSeccompPrefill then (← source_field j "seccomp_prefill").getNat? else pure 0
  let trace : Trace := { id, ops, rlimit, hidden, steer, armRecords, napiBeforePut, allocArmed, pauses, bare, foreign, routes, dstCacheRecords, seccompChild, seccompPrefill }
  -- seccomp design 5: the prefill fixture is the trace process's, outside every
  -- window: never with a network fixture or a steering schedule
  if hasSeccompPrefill && (seccompPrefill == 0 || seccompPrefill > Leanux.Seccomp.Prefill.PREFILL_MAX) then
    throw s!"seccomp_prefill: expected 1..{Leanux.Seccomp.Prefill.PREFILL_MAX}"
  if seccompPrefill > 0 && (trace.net || !steer.isEmpty) then
    throw "seccomp_prefill: never with a network fixture or a steering schedule"
  if (bare || foreign || !routes.isEmpty) && !trace.net then throw "net_fixture: only a network trace has a network fixture"
  -- seccomp design 5: descriptor 8 is the child's KCOV or W8's injector, never both
  if seccompChild && trace.net then throw "seccomp_child: exclusive with a network fixture"
  if trace.ops.any (fun | .seccompProbe _ _ .child _ => true | _ => false) && !seccompChild then
    throw "seccomp_probe in a child needs the seccomp_child fixture"
  if foreign && rlimit < 10 then throw "net_fixture: the foreign-creator fixture needs rlimit_nofile >= 10"
  -- W2 (4.2): the stepped dump socket at fd 8 (reserved 0..8); L's
  -- temporary rtnetlink socket then lands at 9. The foreign-creator fixture
  -- holds 8 and 9 itself, so the two are exclusive.
  if trace.stepped && foreign then throw "a stepped dump and the foreign-creator fixture both need descriptor 8"
  if trace.stepped && rlimit < 9 then throw "a stepped dump needs rlimit_nofile >= 9"
  if trace.stepped && rlimit < 10 && ops.any (fun | .wgCreate | .wgDelete => true | _ => false) then
    throw "a stepped dump with wg_create or wg_delete needs rlimit_nofile >= 10"
  return trace

private def traceSource (j : Json) : Except String Trace := do
  let hasLimit := (j.getObjVal? "rlimit_nofile").isOk
  let hasHidden := (j.getObjVal? "hidden").isOk
  let hasSteer := (j.getObjVal? "steer").isOk
  let hasExpect := (j.getObjVal? "expect").isOk
  let hasArm := (j.getObjVal? "arm_records").isOk
  let hasPlacement := (j.getObjVal? "napi_irq_before_put").isOk
  let hasFixture := (j.getObjVal? "net_fixture").isOk
  let hasArmed := (j.getObjVal? "alloc_armed").isOk
  let hasDst := (j.getObjVal? "dst_cache_records").isOk
  let hasExtension := (j.getObjVal? "domain_extension").isOk
  let hasSeccompChild := (j.getObjVal? "seccomp_child").isOk
  let hasSeccompPrefill := (j.getObjVal? "seccomp_prefill").isOk
  source_fields j ((if hasLimit then ["version", "id", "ops", "rlimit_nofile"] else ["version", "id", "ops"])
    ++ (if hasHidden then ["hidden"] else []) ++ (if hasSteer then ["steer"] else [])
    ++ (if hasExpect then ["expect"] else []) ++ (if hasArm then ["arm_records"] else [])
    ++ (if hasPlacement then ["napi_irq_before_put"] else [])
    ++ (if hasFixture then ["net_fixture"] else [])
    ++ (if hasArmed then ["alloc_armed"] else [])
    ++ (if hasDst then ["dst_cache_records"] else [])
    ++ (if hasExtension then ["domain_extension"] else [])
    ++ (if hasSeccompChild then ["seccomp_child"] else [])
    ++ (if hasSeccompPrefill then ["seccomp_prefill"] else []))
  -- D3: the arm-record switch qualifies the records, so it comes with them
  if hasArm && !hasHidden then throw "arm_records: only with hidden records"
  let armRecords ← if hasArm then (← source_field j "arm_records").getBool? else pure false
  let dstCacheRecords ← if hasDst then (← source_field j "dst_cache_records").getBool? else pure true
  -- The declared failslab-style extension (docs/2026-10-05-a-alloc.md,
  -- section 3, [USER 2026-10-06]): the trace forces task-context allocation
  -- failures; the host checks the schedule, the mirror only its form.
  if hasExtension then
    if (← (← source_field j "domain_extension").getStr?) != "failslab" then throw "domain_extension: expected \"failslab\""
    if !hasSteer then throw "domain_extension: only a steered trace declares it"
  let rlimit ← if hasLimit then source_natField j "rlimit_nofile" 1024 else pure 32
  if rlimit < 8 then throw "rlimit_nofile outside 8..1024"
  if (← (← source_field j "version").getNat?) != 1 then throw "unsupported trace version"
  let id ← (← source_field j "id").getStr?
  if id.isEmpty || id.length > 80 || !id.toList.all (fun c =>
      c.isAlphanum && c.toNat < 128 || c == '_' || c == '-' || c == '.') then
    throw "invalid trace identifier"
  let rawOps ← (← source_field j "ops").getArr?
  if rawOps.isEmpty || rawOps.size > 64 then throw "trace length outside 1..64"
  let mut ops := #[]
  let mut pauses := #[]
  for j in rawOps do
    -- `pause_ms` (1-20) may accompany any operation; the rest is the
    -- operation's own exact source_field set
    let obj ← j.getObj?
    let (j, pause) ← match obj.get? "pause_ms" with
      | some v => do
        let n ← v.getNat?
        if n < 1 || n > PAUSE_MS_MAX then throw "pause_ms outside 1..20"
        pure (Json.obj (obj.erase "pause_ms"), n)
      | none => pure (j, 0)
    ops := ops.push (← parseOperation j ops)
    pauses := pauses.push pause
  traceFinish j id ops pauses rlimit armRecords dstCacheRecords hasHidden hasSteer
    hasPlacement hasFixture hasArmed hasSeccompChild hasSeccompPrefill

private theorem traceSource_eq (j : Json) : traceSource j = Runner.parseTrace j := by
  rfl

private theorem traceFinish_good (j : Json) (id : String) (ops : Array Operation) (pauses : Array Nat)
    (rlimit : Nat) (armRecords dstCacheRecords hasHidden hasSteer hasPlacement hasFixture
      hasArmed hasSeccompChild hasSeccompPrefill : Bool)
    (hs : ∀ op ∈ ops, OperationAddressShape op) :
    Good (traceFinish j id ops pauses rlimit armRecords dstCacheRecords hasHidden hasSteer
      hasPlacement hasFixture hasArmed hasSeccompChild hasSeccompPrefill) TraceAddressShape := by
  unfold traceFinish
  repeat' first
    | parser_trace_goal; exact hs
    | parser_good_goal; with_reducible exact good_abort_bind _ _
    | parser_good_goal; with_reducible exact good_throw _
    | parser_good_goal; with_reducible apply good_if
    | parser_good_goal; with_reducible apply good_bind_any
    | parser_good_goal; with_reducible apply good_pure
    | parser_intro
    | (parser_good_goal; with_reducible split)

theorem parseTrace_shape (j : Json) (trace : Trace)
    (hr : Runner.parseTrace j = .ok trace) : TraceAddressShape trace := by
  have ops (rawOps : Array Json) := parseOps_good rawOps
  unfold parseOps at ops
  simp only [pair_eta, bind_pure] at ops
  have good : Good (traceSource j) TraceAddressShape := by
    unfold traceSource
    repeat' first
      | (parser_good_goal; with_reducible apply traceFinish_good; assumption)
      | parser_good_goal; with_reducible apply good_bind _ _ (ops _)
      | parser_good_goal; with_reducible exact good_abort_bind _ _
      | parser_good_goal; with_reducible exact good_throw _
      | parser_good_goal; with_reducible apply good_if
      | parser_good_goal; with_reducible apply good_bind_any
      | parser_good_goal; with_reducible apply good_pure
      | parser_intro
      | (parser_good_goal; with_reducible split)
    all_goals apply traceFinish_good
    all_goals exact (show OpsShape _ from by assumption)
  exact good trace (by simpa only [traceSource_eq] using hr)

end Leanux.Proofs.WG.Configuration
