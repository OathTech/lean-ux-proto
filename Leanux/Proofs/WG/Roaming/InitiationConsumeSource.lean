import Leanux.Proofs.WG.Roaming.InitiationConsumeErasureSource
import Leanux.Proofs.WG.Roaming.InitiationCryptoEffects

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

private def initiationCommitTail (identity : StaticIdentity) (s timestamp : List UInt8)
    (pid : PeerId) (lookup : InitiationLookup) (dhPeer : Peer) (beforeDh : Campaign2.Snapshot)
    (checked : Peer) (beforeChecks : Campaign2.Snapshot) (now consumption : Int64) :
    WG.M (Option InitiationConsumed) := do
  let last := (← getPeer pid).lastInitiationConsumption
  let diff : Int64 := last - consumption
  if ← branchCmp .consumeLaterTime (diff < 0) diff.toInt 0 then
    setPeer pid { (← getPeer pid) with lastInitiationConsumption := consumption }
  setPeer pid { (← getPeer pid) with handshakeState := HANDSHAKE_CONSUMED_INITIATION }
  let _ ← initiationOut (some pid) (some pid)
  return some ⟨identity, s, timestamp, pid, lookup, dhPeer, beforeDh, checked, beforeChecks, now,
    consumption, ← Campaign2.read⟩

private theorem initiationCommitTail_facts (msg : List UInt8) (identity : StaticIdentity) (s : Key)
    (pid : PeerId) (lookup : InitiationLookup) (dhPeer : Peer) (beforeDh : Campaign2.Snapshot)
    (ck timestamp hash : List UInt8) (checked : Peer) (beforeChecks : Campaign2.Snapshot)
    (now consumption : Int64) (checkedAt : beforeChecks.peerAt pid = some checked)
    (newer : memcmp timestamp checked.latestTimestamp = .gt)
    (allowed : checked.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64 ≤ now) :
    Campaign2.Ensures (initiationCommitTail identity s timestamp pid lookup dhPeer beforeDh checked beforeChecks now consumption)
      (fun view => ∃ q, view.peerAt pid = some q ∧ q.remoteEphemeral = initiationEphemeral msg ∧
        q.remoteIndex = u32le msg 4 ∧ q.latestTimestamp = timestamp ∧ q.chainingKey = ck ∧
        q.hash = hash ∧ q.lastInitiationConsumption = checked.lastInitiationConsumption)
      (fun result observed => ∀ cut, result = some cut →
        cut.committed = observed ∧ cut.identity = identity ∧
        cut.staticPlain = s ∧ cut.timestamp = timestamp ∧ cut.pid = pid ∧
        cut.lookup = lookup ∧ cut.dhPeer = dhPeer ∧ cut.beforeDh = beforeDh ∧
        InitiationCommitFacts msg ck hash cut) := by
  intro g ambient result final after pre run cut returned
  subst result
  obtain ⟨q, resident, ephemeral, remote, stamped, chained, hashed, lastEq⟩ := pre
  have readRun (start : WGWorld) (before : Ambient) :
      (Campaign2.read.run start).run before =
        Except.ok ((Campaign2.snapshot start before, start), before) := rfl
  have hok {α β : Type} (value : α) (next : α → Except Stop β) :
      (Except.ok value >>= next) = next value := rfl
  cases device : g.dev with
  | none => simp [Campaign2.Snapshot.peerAt, Campaign2.snapshot, Campaign2.core, device] at resident
  | some d =>
    change (g.dev.bind fun d => d.peers[pid]?) = some q at resident
    simp only [device, Option.bind_some] at resident
    by_cases later : q.lastInitiationConsumption - consumption < 0
    all_goals
      simp [initiationCommitTail, getPeer, getDev, device, resident, setPeer, modifyDev,
        branchCmp, AmbientM.branchCmp, branch, AmbientM.branch, initiationOut, later, readRun] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      simp only [lastEq] at later
      change (beforeChecks.wg.device.bind fun d => d.peers[pid]?) = some checked at checkedAt
      simp [InitiationCommitFacts, Campaign2.Snapshot.peerAt, Campaign2.snapshot, Campaign2.core,
        checkedAt, newer, allowed, ephemeral, remote, stamped, chained, hashed, lastEq, later]

private def initiationCommitPrefix {α : Type} (msg : List UInt8) (pid : PeerId)
    (checked : Peer) (ck timestamp hash : List UInt8) (next : WG.M α) : WG.M α := do
  setPeer pid { (← getPeer pid) with remoteEphemeral := initiationEphemeral msg }
  if ← branch .consumeNewerTimestamp (memcmp timestamp checked.latestTimestamp == Ordering.gt) then
    setPeer pid { (← getPeer pid) with latestTimestamp := timestamp }
  setPeer pid { (← getPeer pid) with hash := hash, chainingKey := ck, remoteIndex := u32le msg 4 }
  next

private theorem initiationCommitPrefix_facts {α : Type} (msg : List UInt8) (pid : PeerId)
    (checked : Peer) (ck timestamp hash : List UInt8)
    (newer : memcmp timestamp checked.latestTimestamp = .gt)
    (next : WG.M α) (Q : α → Campaign2.Snapshot → Prop)
    (continuation : Campaign2.Ensures next
      (fun view => ∃ q, view.peerAt pid = some q ∧ q.remoteEphemeral = initiationEphemeral msg ∧
        q.remoteIndex = u32le msg 4 ∧ q.latestTimestamp = timestamp ∧ q.chainingKey = ck ∧
        q.hash = hash ∧ q.lastInitiationConsumption = checked.lastInitiationConsumption) Q) :
    Campaign2.Ensures (initiationCommitPrefix msg pid checked ck timestamp hash next)
      (fun view => view.peerAt pid = some checked) Q := by
  intro g ambient result final after resident run
  cases device : g.dev with
  | none => simp [Campaign2.Snapshot.peerAt, Campaign2.snapshot, Campaign2.core, device] at resident
  | some d =>
    change (g.dev.bind fun d => d.peers[pid]?) = some checked at resident
    simp only [device, Option.bind_some] at resident
    simp [initiationCommitPrefix, getPeer, getDev, device, resident, setPeer, modifyDev,
      branch, AmbientM.branch, newer] at run
    apply continuation _ _ _ _ _ ?_ run
    simp [Campaign2.Snapshot.peerAt, Campaign2.snapshot, Campaign2.core]

private theorem initiationPastChecks_run (pid : PeerId) (timestamp : List UInt8)
    (g : WGWorld) (ambient : Ambient) (d : Device) (p : Peer) (now : Int64) (middle : Ambient)
    (device : g.dev = some d) (resident : d.peers[pid]? = some p)
    (clock : (AmbientM.hiddenClock64 .floodNow).run ambient = .ok (now, middle))
    (newer : memcmp timestamp p.latestTimestamp = .gt)
    (flood : ¬p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64 > now)
    (next : Peer → Campaign2.Snapshot → Int64 → WG.M (Option InitiationConsumed)) :
    let replayMarked := {middle with steps := middle.steps.push {
      decision := .consumeReplay, outcome := false, netRx := middle.netRxSection}}
    let floodMarked := {replayMarked with steps := replayMarked.steps.push {
      decision := .consumeFlood, outcome := false,
      operands := some ((p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64).toInt, now.toInt),
      netRx := replayMarked.netRxSection}}
    ((do
      let checked ← getPeer pid
      let beforeChecks ← Campaign2.read
      let replay := memcmp timestamp checked.latestTimestamp != Ordering.gt
      let floodLhs : Int64 := checked.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64
      let seen ← hiddenClock64 .floodNow
      if ← WG.orM (branch .consumeReplay replay)
          (branchCmp .consumeFlood (floodLhs > seen) floodLhs.toInt seen.toInt) then
        let _ ← initiationOut (some pid) none
        return none
      next checked beforeChecks seen : WG.M (Option InitiationConsumed)).run g).run ambient =
      ((next p (Campaign2.snapshot g ambient) now).run g).run floodMarked := by
  have hok {α β : Type} (value : α) (next : α → Except Stop β) :
      (Except.ok value >>= next) = next value := rfl
  have readRun (start : WGWorld) (before : Ambient) :
      (Campaign2.read.run start).run before =
        Except.ok ((Campaign2.snapshot start before, start), before) := rfl
  have liftClock (site : HiddenSite) (start : WGWorld) (before : Ambient) :
      ((hiddenClock64 site : WG.M Int64).run start).run before =
        ((AmbientM.hiddenClock64 site).run before >>= fun (value, after) =>
          Except.ok ((value, start), after)) := rfl
  let replayMarked := {middle with steps := middle.steps.push {
    decision := .consumeReplay, outcome := false, netRx := middle.netRxSection}}
  let floodMarked := {replayMarked with steps := replayMarked.steps.push {
    decision := .consumeFlood, outcome := false,
    operands := some ((p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64).toInt, now.toInt),
    netRx := replayMarked.netRxSection}}
  have bindRun {α β : Type} (action : WG.M α) (next : α → WG.M β)
      (state : WGWorld) (inputs : Ambient) :
      (((action >>= next).run state).run inputs) =
        (((action.run state).run inputs) >>= fun ((value, current), after) =>
          ((next value).run current).run after) := rfl
  have getRun : ((getPeer pid).run g).run ambient = .ok ((p, g), ambient) := by
    simp [getPeer, getDev, device, resident]
    rfl
  have gateRun :
      ((WG.orM (branch .consumeReplay (memcmp timestamp p.latestTimestamp != Ordering.gt))
        (branchCmp .consumeFlood (p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64 > now)
          (p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64).toInt now.toInt)).run g).run middle =
          .ok ((false, g), floodMarked) := by
    simp [WG.orM, newer, flood, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
      floodMarked, replayMarked]
    rfl
  rw [bindRun, getRun]
  simp only [hok]
  rw [bindRun, readRun]
  simp only [hok]
  rw [bindRun, liftClock, clock]
  simp only [hok]
  rw [bindRun, gateRun]
  rfl

private theorem initiationAfterWrites_facts (msg : List UInt8) (identity : StaticIdentity) (s : Key)
    (pid : PeerId) (lookup : InitiationLookup) (dhPeer : Peer) (beforeDh : Campaign2.Snapshot)
    (ck timestamp hash : List UInt8) (checked : Peer) (beforeChecks : Campaign2.Snapshot)
    (now : Int64) (checkedAt : beforeChecks.peerAt pid = some checked)
    (newer : memcmp timestamp checked.latestTimestamp = .gt)
    (allowed : checked.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64 ≤ now) :
    Campaign2.Ensures (do
      let consumption ← hiddenClock64 .consumptionNow
      initiationCommitTail identity s timestamp pid lookup dhPeer beforeDh checked beforeChecks now consumption)
      (fun view => ∃ q, view.peerAt pid = some q ∧ q.remoteEphemeral = initiationEphemeral msg ∧
        q.remoteIndex = u32le msg 4 ∧ q.latestTimestamp = timestamp ∧ q.chainingKey = ck ∧
        q.hash = hash ∧ q.lastInitiationConsumption = checked.lastInitiationConsumption)
      (fun result observed => ∀ cut, result = some cut →
        cut.committed = observed ∧ cut.identity = identity ∧
        cut.staticPlain = s ∧ cut.timestamp = timestamp ∧ cut.pid = pid ∧
        cut.lookup = lookup ∧ cut.dhPeer = dhPeer ∧ cut.beforeDh = beforeDh ∧
        InitiationCommitFacts msg ck hash cut) := by
  intro current inputs value done last fields execution
  have hok {α β : Type} (value : α) (next : α → Except Stop β) :
      (Except.ok value >>= next) = next value := rfl
  have herror {α β : Type} (err : Stop) (next : α → Except Stop β) :
      (Except.error err >>= next) = (Except.error err : Except Stop β) := rfl
  have liftClock (site : HiddenSite) (start : WGWorld) (before : Ambient) :
      ((hiddenClock64 site : WG.M Int64).run start).run before =
        ((AmbientM.hiddenClock64 site).run before >>= fun (value, after) =>
          Except.ok ((value, start), after)) := rfl
  change (((hiddenClock64 .consumptionNow : WG.M Int64).run current).run inputs >>=
    fun ((consumption, current'), inputs') =>
      ((initiationCommitTail identity s timestamp pid lookup dhPeer beforeDh checked
        beforeChecks now consumption).run current').run inputs') =
      .ok ((value, done), last) at execution
  cases clock2 : (AmbientM.hiddenClock64 .consumptionNow).run inputs with
  | error err => simp only [liftClock, clock2, herror] at execution; cases execution
  | ok pair =>
    rcases pair with ⟨consumption, beforeTail⟩
    simp only [liftClock, clock2, hok] at execution
    exact initiationCommitTail_facts msg identity s pid lookup dhPeer beforeDh ck timestamp hash
      checked beforeChecks now consumption checkedAt newer allowed
      current beforeTail value done last fields execution

private def initiationChecks (pid : PeerId) (timestamp : List UInt8)
    (next : Peer → Campaign2.Snapshot → Int64 → WG.M (Option InitiationConsumed)) : WG.M (Option InitiationConsumed) := do
  let checked ← getPeer pid
  let beforeChecks ← Campaign2.read
  let replay := memcmp timestamp checked.latestTimestamp != Ordering.gt
  let floodLhs : Int64 := checked.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64
  let seen ← hiddenClock64 .floodNow
  if ← WG.orM (branch .consumeReplay replay)
      (branchCmp .consumeFlood (floodLhs > seen) floodLhs.toInt seen.toInt) then
    let _ ← initiationOut (some pid) none
    return none
  next checked beforeChecks seen

private theorem initiationChecks_facts (pid : PeerId) (timestamp : List UInt8)
    (next : Peer → Campaign2.Snapshot → Int64 → WG.M (Option InitiationConsumed))
    (Q : Option InitiationConsumed → Campaign2.Snapshot → Prop)
    (rejected : ∀ view, Q none view)
    (continuation : ∀ checked beforeChecks now,
      beforeChecks.peerAt pid = some checked →
      memcmp timestamp checked.latestTimestamp = .gt →
      checked.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64 ≤ now →
      Campaign2.Ensures (next checked beforeChecks now)
        (fun view => view.peerAt pid = some checked) Q) :
    Campaign2.Ensures (initiationChecks pid timestamp next) (fun _ => True) Q := by
  intro g ambient result final after _ run
  have fail (peer : Option PeerId) (start : WGWorld) (before : Ambient)
      (done : WGWorld) (last : Ambient) :
      ((do let _ ← initiationOut peer none; pure (none : Option InitiationConsumed) : WG.M _).run start).run before =
        .ok ((result, done), last) → Q result (Campaign2.snapshot done last) := by
    intro execution
    change (((initiationOut peer none).run start).run before >>= fun ((_, current), inputs) =>
      Except.ok ((none, current), inputs)) = _ at execution
    cases out : ((initiationOut peer none).run start).run before with
    | error err => rw [out] at execution; cases execution
    | ok pair =>
      rcases pair with ⟨⟨value, current⟩, inputs⟩
      rw [out] at execution
      cases execution
      exact rejected _
  have hok {α β : Type} (value : α) (next : α → Except Stop β) :
      (Except.ok value >>= next) = next value := rfl
  have herror {α β : Type} (err : Stop) (next : α → Except Stop β) :
      (Except.error err >>= next) = (Except.error err : Except Stop β) := rfl
  have readRun (start : WGWorld) (before : Ambient) :
      (Campaign2.read.run start).run before =
        Except.ok ((Campaign2.snapshot start before, start), before) := rfl
  have liftClock (site : HiddenSite) (start : WGWorld) (before : Ambient) :
      ((hiddenClock64 site : WG.M Int64).run start).run before =
        ((AmbientM.hiddenClock64 site).run before >>= fun (value, after) =>
          Except.ok ((value, start), after)) := rfl
  have bindRun {α β : Type} (action : WG.M α) (next : α → WG.M β)
      (state : WGWorld) (inputs : Ambient) :
      (((action >>= next).run state).run inputs) =
        (((action.run state).run inputs) >>= fun ((value, current), after) =>
          ((next value).run current).run after) := rfl
  unfold initiationChecks at run
  cases device : g.dev with
  | none =>
    simp [getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [getPeer, getDev, device, resident, invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      have original := run
      have getRun : ((getPeer pid).run g).run ambient = .ok ((p, g), ambient) := by
        simp [getPeer, getDev, device, resident]
        rfl
      rw [bindRun, getRun] at run
      simp only [hok] at run
      rw [bindRun, readRun] at run
      simp only [hok] at run
      rw [bindRun, liftClock] at run
      cases clock : (AmbientM.hiddenClock64 .floodNow).run ambient with
      | error err =>
        rw [clock] at run
        simp only [herror] at run
        cases run
      | ok pair =>
        rcases pair with ⟨now, middle⟩
        rw [clock] at run
        simp only [hok] at run
        by_cases newer : memcmp timestamp p.latestTimestamp = .gt
        · by_cases flood : p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64 > now
          · simp [WG.orM, newer, flood, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp] at run
            exact fail _ _ _ _ _ run
          · rw [initiationPastChecks_run pid timestamp g ambient d p now middle device resident clock newer flood next] at original
            have checkedAt : (Campaign2.snapshot g ambient).peerAt pid = some p := by
              simp [Campaign2.Snapshot.peerAt, Campaign2.snapshot, Campaign2.core, device, resident]
            let replayMarked := {middle with steps := middle.steps.push {
              decision := .consumeReplay, outcome := false, netRx := middle.netRxSection}}
            let floodMarked := {replayMarked with steps := replayMarked.steps.push {
              decision := .consumeFlood, outcome := false,
              operands := some ((p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64).toInt, now.toInt),
              netRx := replayMarked.netRxSection}}
            exact continuation p (Campaign2.snapshot g ambient) now checkedAt newer (Int64.not_lt.mp flood)
              g floodMarked result final after checkedAt original
        · simp [WG.orM, newer, branch, AmbientM.branch] at run
          exact fail _ _ _ _ _ run

theorem initiationFinish_facts (msg : List UInt8) (identity : StaticIdentity) (s : Key)
    (pid : PeerId) (lookup : InitiationLookup) (dhPeer : Peer) (beforeDh : Campaign2.Snapshot)
    (ck timestamp hash : List UInt8) :
    Campaign2.Ensures (initiationFinish msg identity s pid lookup dhPeer beforeDh ck timestamp hash)
      (fun _ => True)
      (fun result observed => ∀ cut, result = some cut →
        cut.committed = observed ∧ cut.identity = identity ∧
        cut.staticPlain = s ∧ cut.timestamp = timestamp ∧ cut.pid = pid ∧
        cut.lookup = lookup ∧ cut.dhPeer = dhPeer ∧ cut.beforeDh = beforeDh ∧
        InitiationCommitFacts msg ck hash cut) := by
  let Q : Option InitiationConsumed → Campaign2.Snapshot → Prop :=
    fun result observed => ∀ completed, result = some completed →
      completed.committed = observed ∧ completed.identity = identity ∧
      completed.staticPlain = s ∧ completed.timestamp = timestamp ∧ completed.pid = pid ∧
      completed.lookup = lookup ∧ completed.dhPeer = dhPeer ∧ completed.beforeDh = beforeDh ∧
      InitiationCommitFacts msg ck hash completed
  change Campaign2.Ensures (initiationChecks pid timestamp (fun checked beforeChecks now =>
    initiationCommitPrefix msg pid checked ck timestamp hash (do
      let consumption ← hiddenClock64 .consumptionNow
      initiationCommitTail identity s timestamp pid lookup dhPeer beforeDh checked beforeChecks now consumption)))
      (fun _ => True) Q
  apply initiationChecks_facts pid timestamp _ Q
  · intro view completed impossible
    cases impossible
  · intro checked beforeChecks now checkedAt newer allowed
    exact initiationCommitPrefix_facts msg pid checked ck timestamp hash newer _ Q
      (initiationAfterWrites_facts msg identity s pid lookup dhPeer beforeDh ck timestamp hash
        checked beforeChecks now checkedAt newer allowed)


theorem initiationConsume_facts (msg : List UInt8) :
    Campaign2.Ensures (initiationConsume msg) (fun _ => True)
      (fun result observed => ∀ cut, result = some cut →
        cut.committed = observed ∧ InitiationConsumedFacts msg cut) := by
  let Q : Option InitiationConsumed → Campaign2.Snapshot → Prop :=
    fun result observed => ∀ cut, result = some cut →
      cut.committed = observed ∧ InitiationConsumedFacts msg cut
  have step {α : Type} (action : WG.M α) (next : α → WG.M (Option InitiationConsumed))
      (A : α → Prop)
      (first : ∀ g ambient value current after,
        (action.run g).run ambient = .ok ((value, current), after) → A value)
      (rest : ∀ value, A value → Campaign2.Ensures (next value) (fun _ => True) Q) :
      Campaign2.Ensures (action >>= next) (fun _ => True) Q := by
    intro g ambient value final after _ run
    change ((action.run g).run ambient >>= fun ((x, current), inputs) =>
      ((next x).run current).run inputs) = _ at run
    cases firstRun : (action.run g).run ambient with
    | error err => rw [firstRun] at run; cases run
    | ok pair =>
      rcases pair with ⟨⟨x, current⟩, inputs⟩
      rw [firstRun] at run
      exact rest x (first g ambient x current inputs firstRun) current inputs value final after trivial run
  have gate (site : Decision) (value : Bool) (next : Bool → WG.M (Option InitiationConsumed))
      (rest : Campaign2.Ensures (next value) (fun _ => True) Q) :
      Campaign2.Ensures (branch site value >>= next) (fun _ => True) Q := by
    apply step _ _ (fun out => out = value)
    · intro g ambient out current after run
      simp [branch, AmbientM.branch] at run
      exact (congrArg (fun x => x.1.1) (Except.ok.inj run)).symm
    · intro out same
      subst out
      exact rest
  have fail (peer : Option PeerId) :
      Campaign2.Ensures (do let _ ← initiationOut peer none; pure none)
        (fun _ => True) Q := by
    intro g ambient value final after _ run cut selected
    change (((initiationOut peer none).run g).run ambient >>= fun ((_, current), inputs) =>
      Except.ok ((none, current), inputs)) = _ at run
    cases out : ((initiationOut peer none).run g).run ambient with
    | error err => rw [out] at run; cases run
    | ok pair =>
      rw [out] at run
      cases run
      cases selected
  have ephemeral (copy : Bool) (e ck hash : List UInt8) :
      ∀ g ambient value current after,
        ((messageEphemeral copy e ck hash).run g).run ambient = .ok ((value, current), after) →
        value = (responseFirst ck e, noiseHash (hash ++ e)) := by
    intro g ambient value current after run
    simp [messageEphemeral, kdf, responseKdf_one, kdfOut, WG.orM, branch, AmbientM.branch] at run
    exact (congrArg (fun x => x.1.1) (Except.ok.inj run)).symm
  have dh (ck priv pub : List UInt8) :
      ∀ g ambient value current after,
        ((mixDh true ck priv pub).run g).run ambient = .ok ((value, current), after) →
        value = (if (curve25519 priv pub).2 then
          some (responseFirst ck (curve25519 priv pub).1, responseSecond ck (curve25519 priv pub).1) else none) := by
    intro g ambient value current after run
    cases ok : (curve25519 priv pub).2 <;>
      simp [mixDh, ok, kdf, initiationKdf_two, kdfOut, WG.orM, branch, AmbientM.branch] at run ⊢
    all_goals exact (congrArg (fun x => x.1.1) (Except.ok.inj run)).symm
  have decrypt (sealed key hash : List UInt8) :
      ∀ g ambient value current after,
        ((messageDecrypt sealed key hash).run g).run ambient = .ok ((value, current), after) →
        value = (aeadDecrypt key noiseNonce sealed hash).map (fun plain => (plain, noiseHash (hash ++ sealed))) := by
    intro g ambient value current after run
    cases dec : aeadDecrypt key noiseNonce sealed hash <;>
      simp [messageDecrypt, dec, branch, AmbientM.branch] at run ⊢
    all_goals exact (congrArg (fun x => x.1.1) (Except.ok.inj run)).symm
  have precomputed (ck key : List UInt8) :
      ∀ g ambient value current after,
        ((mixPrecomputedDh ck key).run g).run ambient = .ok ((value, current), after) →
        value = (if key = List.replicate 32 0 then none
          else some (responseFirst ck key, responseSecond ck key)) := by
    intro g ambient value current after run
    have zero : (noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.zeroKey) = List.replicate 32 0 := rfl
    by_cases same : key = List.replicate 32 0
    · simp [mixPrecomputedDh, zero, same, kdf, initiationKdf_two, kdfOut, WG.orM, branch, AmbientM.branch] at run ⊢
      exact (congrArg (fun x => x.1.1) (Except.ok.inj run)).symm
    · have different : (key == (noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.zeroKey)) = false := by
        change (key == List.replicate 32 0) = false
        exact beq_eq_false_iff_ne.mpr same
      rw [ite_eq_right same]
      simp [mixPrecomputedDh, different, kdf, initiationKdf_two, kdfOut, WG.orM, branch, AmbientM.branch] at run
      exact (congrArg (fun x => x.1.1) (Except.ok.inj run)).symm
  let capture (pid : PeerId) : WG.M (Peer × Campaign2.Snapshot) := do
    let p ← getPeer pid
    let view ← Campaign2.read
    pure (p, view)
  have captured (pid : PeerId) : ∀ g ambient value current after,
      ((capture pid).run g).run ambient = .ok ((value, current), after) →
      value.2.peerAt pid = some value.1 := by
    intro g ambient value current after run
    have readRun (start : WGWorld) (before : Ambient) :
      (Campaign2.read.run start).run before = .ok ((Campaign2.snapshot start before, start), before) := rfl
    cases device : g.dev with
    | none => simp [capture, getPeer, getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      cases resident : d.peers[pid]? with
      | none => simp [capture, getPeer, getDev, device, resident, invariant, AmbientM.invariant] at run; cases run
      | some p =>
        simp [capture, getPeer, getDev, device, resident, readRun] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        simp [Campaign2.Snapshot.peerAt, Campaign2.snapshot, Campaign2.core, device, resident]
  have source : initiationConsume msg = (do
    let identity := (← getDev).staticIdentity
    if ← branch .consumeNoIdentity !identity.hasIdentity then
      let _ ← initiationOut none none
      return none
    let (ck, hash) ← messageEphemeral true (initiationEphemeral msg) handshakeInitChainingKey
      (noiseHash (handshakeInitHash ++ identity.staticPublic))
    let es ← mixDh true ck identity.staticPrivate (initiationEphemeral msg)
    if ← branch .consumeEsFailed es.isNone then
      let _ ← initiationOut none none
      return none
    let some (ck, key) := es | invariant "unreachable"
    let st ← messageDecrypt ((msg.drop 40).take 48) key hash
    if ← branch .consumeStaticFailed st.isNone then
      let _ ← initiationOut none none
      return none
    let some (s, hash) := st | invariant "unreachable"
    let lookup ← initiationLookup s
    let peer := lookup.result
    if ← branch .consumeNoPeer peer.isNone then
      let _ ← initiationOut none none
      return none
    let some pid := peer | invariant "unreachable"
    let (dhPeer, beforeDh) ← capture pid
    let ss ← mixPrecomputedDh ck dhPeer.precomputedStaticStatic
    if ← branch .consumeSsFailed ss.isNone then
      let _ ← initiationOut peer none
      return none
    let some (ckSs, key) := ss | invariant "unreachable"
    let ts ← messageDecrypt ((msg.drop 88).take 28) key hash
    if ← branch .consumeTimestampFailed ts.isNone then
      let _ ← initiationOut peer none
      return none
    let some (t, hashT) := ts | invariant "unreachable"
    initiationFinish msg identity s pid lookup dhPeer beforeDh ckSs t hashT : WG.M (Option InitiationConsumed)) := by
      simp only [initiationConsume, capture, initiationEphemeral, bind_assoc, pure_bind]
      rfl
  rw [source]
  change Campaign2.Ensures _ (fun _ => True) Q
  apply step getDev _ (fun _ => True) (by intros; trivial)
  intro d _
  apply gate
  cases identity : d.staticIdentity.hasIdentity with
  | false => simpa only [identity, Bool.not_false, ite_true] using fail none
  | true =>
    simp only [ Bool.not_true, Bool.false_eq_true, ite_false]
    apply step _ _ _ (ephemeral _ _ _ _)
    intro first firstEq
    subst first
    apply step _ _ _ (dh _ _ _)
    intro es esEq
    subst es
    apply gate
    cases dhOk : (curve25519 d.staticIdentity.staticPrivate (initiationEphemeral msg)).2 with
    | false => simpa only [dhOk, Bool.false_eq_true, ite_false, Option.isNone_none, ite_true] using fail none
    | true =>
      simp only [ ite_true, Option.isNone_some, Bool.false_eq_true, ite_false]
      apply step _ _ _ (decrypt _ _ _)
      intro st stEq
      subst st
      apply gate
      cases staticDec : aeadDecrypt _ noiseNonce ((msg.drop 40).take 48) _ with
      | none => simpa only [staticDec, Option.map_none, Option.isNone_none, ite_true] using fail none
      | some plain =>
        simp only [ Option.map_some, Option.isNone_some, Bool.false_eq_true, ite_false]
        apply step _ _ _ (fun g ambient out current after run =>
          initiationLookup_facts plain g ambient out current after trivial run)
        intro lookup lookupFacts
        apply gate
        cases selected : lookup.result with
        | none => simpa only [selected, Option.isNone_none, ite_true] using fail none
        | some pid =>
          simp only [ Option.isNone_some, Bool.false_eq_true, ite_false]
          apply step _ _ _ (captured pid)
          intro pair beforeDhFact
          rcases pair with ⟨dhPeer, beforeDh⟩
          apply step _ _ _ (precomputed _ _)
          intro ss ssEq
          subst ss
          apply gate
          by_cases nonzero : dhPeer.precomputedStaticStatic = List.replicate 32 0
          · simpa only [nonzero, ite_true, Option.isNone_none] using fail (some pid)
          · simp only [nonzero, ite_false, Option.isNone_some, Bool.false_eq_true]
            apply step _ _ _ (decrypt _ _ _)
            intro ts tsEq
            subst ts
            apply gate
            cases timestampDec : aeadDecrypt _ noiseNonce ((msg.drop 88).take 28) _ with
            | none => simpa only [timestampDec, Option.map_none, Option.isNone_none, ite_true] using fail (some pid)
            | some timestamp =>
              simp only [ Option.map_some, Option.isNone_some, Bool.false_eq_true, ite_false]
              intro g ambient result final after _ run cut returned
              obtain ⟨committed, identityEq, plainEq, timeEq, pidEq, lookupEq, dhEq, beforeEq, facts⟩ :=
                initiationFinish_facts msg d.staticIdentity plain pid lookup dhPeer beforeDh _ timestamp _
                  g ambient result final after trivial run cut returned
              refine ⟨committed, ?_⟩
              simp only [InitiationConsumedFacts, identityEq, plainEq, timeEq, pidEq, lookupEq, dhEq, beforeEq]
              exact ⟨identity, dhOk, staticDec, lookupFacts pid selected, beforeDhFact,
                nonzero, timestampDec, facts⟩

end Leanux.Proofs.WG.Roaming
