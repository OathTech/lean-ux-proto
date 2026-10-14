import Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit
import Leanux.Proofs.WG.Lifetimes.TimerCallbacks
import Leanux.Proofs.WG.Environment.TimerSource

/-! Timer selection and execution at the actual environment boundary. Saved-map
scans precede selection/effects, and the timer is detached by the original
caller before its callback. Both recorded and placeholder finite loops retain
all early exits, records, scheduler entries and failed access prefixes. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

abbrev getDevSavedAudit : AuditM Device := auditFocus (liftPrefix getDev)

theorem getDevSavedAudit_erases : ErasesPrefix getDevSavedAudit getDev :=
  auditFocus_erases (erasesPrefix_lift _)

theorem getDevSavedAudit_spec : PrefixEnsures AuditInv AuditSafe getDevSavedAudit
    (fun d h w => AuditInv h w ∧ SavedPeers d.peers.toList (identityView w)) :=
  (auditFocus_ensures (getDev_saved_spec allocationAmbient (fun _ => True))).consequence
    (fun _ _ hi => ⟨⟨hi.1, trivial⟩, hi.2⟩)
    (fun _ _ _ hi => ⟨⟨hi.1.1, hi.2⟩, hi.1.2.2⟩)

def duePeersAudit (d : Device) (t : PeerTimer) (jHi : UInt64) : AuditM (List PeerId) :=
  auditFocus (savedPeerLookupFlatMap d.peers
    (fun pid p => if (p.timer t).any (fun e => timeBefore e jHi) then [pid] else []) d.peerList)

def dueEntriesAudit (d : Device) (jHi : UInt64) : AuditM (List (UInt64 × PeerId × PeerTimer)) :=
  auditFocus (savedPeerLookupFlatMap d.peers (fun pid p =>
    PeerTimer.all.filterMap fun t => (p.timer t).bind fun e =>
      if timeBefore e jHi then some (e, pid, t) else none) d.peerList)

theorem duePeersAudit_erases (d : Device) (t : PeerTimer) (jHi : UInt64) :
    ErasesPrefix (duePeersAudit d t jHi) (pure (d.peerList.filter fun pid =>
      match d.peers.get? pid >>= (·.timer t) with
      | some e => timeBefore e jHi | none => false)) := by
  have he := auditFocus_erases (savedPeerLookupFlatMap_erases d.peers
    (fun pid p => if (p.timer t).any (fun e => timeBefore e jHi) then [pid] else []) d.peerList)
  have eqs : ∀ ids : List PeerId,
      ids.flatMap (fun pid => (d.peers[pid]?).toList.flatMap
        (fun p => if (p.timer t).any (fun e => timeBefore e jHi) then [pid] else [])) =
      ids.filter (fun pid => match d.peers.get? pid >>= (·.timer t) with
        | some e => timeBefore e jHi | none => false) := by
    intro ids
    induction ids with
    | nil => rfl
    | cons pid ids ih =>
      cases hp : d.peers[pid]? with
      | none => simp [Std.TreeMap.get?_eq_getElem?, hp, ih]
      | some p => cases ht : p.timer t <;> simp [Std.TreeMap.get?_eq_getElem?, hp, ht, ih] <;> split <;> simp_all
  simpa only [duePeersAudit, eqs] using he

theorem dueEntriesAudit_erases (d : Device) (jHi : UInt64) :
    ErasesPrefix (dueEntriesAudit d jHi) (pure (Environment.dueEntries d jHi)) := by
  have he := auditFocus_erases (savedPeerLookupFlatMap_erases d.peers (fun pid p =>
    PeerTimer.all.filterMap fun t => (p.timer t).bind fun e =>
      if timeBefore e jHi then some (e, pid, t) else none) d.peerList)
  have eqs : d.peerList.flatMap (fun pid => (d.peers[pid]?).toList.flatMap (fun p =>
      PeerTimer.all.filterMap fun t => (p.timer t).bind fun e =>
        if timeBefore e jHi then some (e, pid, t) else none)) = Environment.dueEntries d jHi := by
    unfold Environment.dueEntries
    apply congrArg (fun f => d.peerList.flatMap f)
    funext pid
    cases hp : d.peers[pid]? <;> simp [Std.TreeMap.get?_eq_getElem?, hp]
  simpa only [dueEntriesAudit, eqs] using he

theorem duePeersAudit_spec (d : Device) (t : PeerTimer) (jHi : UInt64) :
    PrefixEnsures (fun h w => AuditInv h w ∧ SavedPeers d.peers.toList (identityView w))
      AuditSafe (duePeersAudit d t jHi) (fun _ => AuditInv) :=
  (auditFocus_ensures (savedPeerLookupFlatMap_spec allocationAmbient (fun _ => True) d.peers _ _)).consequence
    (fun _ _ hi => ⟨⟨hi.1.1, trivial, hi.2⟩, hi.1.2⟩)
    (fun _ _ _ hi => ⟨hi.1.1, hi.2⟩)

theorem dueEntriesAudit_spec (d : Device) (jHi : UInt64) :
    PrefixEnsures (fun h w => AuditInv h w ∧ SavedPeers d.peers.toList (identityView w))
      AuditSafe (dueEntriesAudit d jHi) (fun _ => AuditInv) :=
  (auditFocus_ensures (savedPeerLookupFlatMap_spec allocationAmbient (fun _ => True) d.peers _ _)).consequence
    (fun _ _ hi => ⟨⟨hi.1.1, trivial, hi.2⟩, hi.1.2⟩)
    (fun _ _ _ hi => ⟨hi.1.1, hi.2⟩)

def runTimerSectionAudit (worker : Worker) (body : AuditM Unit) : AuditM Unit := do
  if worker.timer?.isNone then liftPrefix (invariant s!"{worker.symbol} is not a timer callback")
  liftPrefix (modify fun s => {s with fired := s.fired.push worker.symbol})
  runWorkerPrefix worker body

theorem runTimerSectionAudit_erases (worker : Worker) (he : ErasesPrefix body originalBody) :
    ErasesPrefix (runTimerSectionAudit worker body) (Env.runTimerSection worker originalBody) := by
  unfold runTimerSectionAudit Env.runTimerSection
  repeat' first
    | with_reducible exact runWorkerPrefix_erases worker he
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem runTimerSectionAudit_preserves (worker : Worker) (hb : PrefixPreserves AuditInv AuditSafe body) :
    PrefixPreserves AuditInv AuditSafe (runTimerSectionAudit worker body) := by
  unfold runTimerSectionAudit
  repeat' first
    | with_reducible exact runWorkerPrefix_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he) worker hb
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

def fireTimerAfterScanAudit (worker : Worker) (t : PeerTimer) (jHi : UInt64)
    (due : List PeerId) : AuditM Unit := do
  let named ← match ← liftPrefix (peekUnit worker) with
    | some u =>
      match (← liftPrefix get).timerUnits.find? (·.1 == u) with
      | some (_, pid, t') =>
        if t' != t then liftPrefix (throw (.hidden s!"a section of {worker.symbol} for another timer of peer {pid}"))
        pure (some pid)
      | none => liftPrefix (throw (.hidden s!"a section of {worker.symbol} for a timer the mirror never armed ({u})"))
    | none => pure none
  match named with
  | some pid =>
    if !due.contains pid then
      liftPrefix (throw (.hidden s!"a section of {worker.symbol} for peer {pid}, whose timer is not pending with expires before jiffies {jHi}"))
    auditFocus (delTimerPrefix pid t)
    runTimerSectionAudit worker (auditFocus (timerCallbackPrefix pid t))
  | none =>
    match due with
    | [pid] =>
      auditFocus (delTimerPrefix pid t)
      runTimerSectionAudit worker (auditFocus (timerCallbackPrefix pid t))
    | [] => liftPrefix (throw (.hidden s!"a section of {worker.symbol}, but no peer's timer is pending with expires before jiffies {jHi}"))
    | _ => liftPrefix (unsupported s!"several peers' timers for {worker.symbol} due in one pass (their order)")

def fireTimerAudit (worker : Worker) (jHi : UInt64) : AuditM Unit := do
  let some t := worker.timer? | liftPrefix (invariant s!"{worker.symbol} is not a timer callback")
  let d ← getDevSavedAudit
  let due ← duePeersAudit d t jHi
  fireTimerAfterScanAudit worker t jHi due

def runTimersAudit (jHi : UInt64) : AuditM Bool := do
  liftPrefix (modify fun w => {w with queuedThisCall := []})
  if (← liftPrefix getK).wg.isNone then return false
  let startOf (w : Worker) := (HiddenSite.sectionStart w).info.id
  let mut fired := false
  for _ in [0:(← liftPrefix recordBudget)] do
    let some site ← liftPrefix Env.peekNextSite | break
    let d ← liftPrefix getDev
    if let some w := Env.timerSectionOf site then
      if w == .clearPeerWorker then
        if d.clearWorkQueue.isEmpty then break
        runOneClearWorkerAudit
      else
        fireTimerAudit w jHi
        fired := true
    else if !fired then break
    else if site == startOf .sendWorker && !d.sendWorkQueue.isEmpty then runOneSendWorkerAudit
    else
      runCryptWorkersAudit
      if (← liftPrefix Env.peekNextSite) == some site then break
  if fired then
    liftPrefix Env.deliverSent
    let d ← liftPrefix getDev
    if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
      liftPrefix (unsupported "work a timer queued outlived the guest's wait")
  return fired

def runTimersPlaceholderAudit (jHi : UInt64) : AuditM Unit := do
  liftPrefix (modify fun w => {w with queuedThisCall := []})
  if (← liftPrefix getK).wg.isNone then return
  let pending := (← liftPrefix getDev).peers.size * PeerTimer.all.length
  for _ in [0:pending + 1] do
    let d ← getDevSavedAudit
    let due ← dueEntriesAudit d jHi
    let first := Environment.firstDue due
    let some (_, pid, t) := first | break
    auditFocus (delTimerPrefix pid t)
    runTimerSectionAudit (← liftPrefix (Env.timerWorker t)) (auditFocus (timerCallbackPrefix pid t))
  runCryptWorkersAudit
  runSendWorkersAudit
  for _ in [0:(← liftPrefix getDev).clearWorkQueue.length + 1] do
    if (← liftPrefix getDev).clearWorkQueue.isEmpty then break
    runOneClearWorkerAudit

def idleTimersAudit : AuditM Unit := do
  let w ← liftPrefix get
  if w.hidden.isNone then
    discard <| runTimersAudit (w.jiffiesLast.getD 0 + w.timing.traceBound.toUInt64 + w.timing.advanceWait.toUInt64)
    return
  let some jEnd ← liftPrefix (peekSiteU64 .jiffiesEnd)
    | liftPrefix (throw (.hidden "no end-of-wait jiffies record (kind 310) in this operation"))
  discard <| runTimersAudit jEnd
  let j ← liftPrefix (hiddenJiffies .jiffiesEnd)
  if j != jEnd then liftPrefix (invariant "the end-of-wait jiffies record changed between the peek and the read")
  liftPrefix (modify fun w => {w with jiffiesLast := some j})

abbrev advanceAudit (ticks : Nat) : AuditM Int := liftPrefix (Env.advance ticks)

def afterAdvanceAudit : AuditM Unit := do
  let w ← liftPrefix get
  if w.hidden.isNone then
    let jHi := w.jiffiesLast.getD 0 + w.timing.advanceWait.toUInt64
    if w.hiddenPlaceholders then runTimersPlaceholderAudit jHi else discard <| runTimersAudit jHi
    return
  let some jEnd ← liftPrefix (peekSiteU64 .jiffiesEnd)
    | liftPrefix (throw (.hidden "no end-of-wait jiffies record (kind 310) in this wg_advance"))
  discard <| runTimersAudit jEnd
  let j ← liftPrefix (hiddenJiffies .jiffiesEnd)
  if j != jEnd then liftPrefix (invariant "the end-of-wait jiffies record changed between the peek and the read")
  liftPrefix (modify fun w => {w with jiffiesLast := some j})

theorem fireTimerAfterScanAudit_erases (worker : Worker) (t : PeerTimer) (jHi : UInt64) (due : List PeerId) :
    ErasesPrefix (fireTimerAfterScanAudit worker t jHi due) (Environment.fireTimerAfterScan worker t jHi due) := by
  unfold fireTimerAfterScanAudit Environment.fireTimerAfterScan
  simp only [bind_assoc, pure_bind]
  repeat' first
    | with_reducible exact getDevSavedAudit_erases
    | with_reducible apply erasesPrefix_bind_pure (duePeersAudit_erases _ _ _)
    | with_reducible apply erasesPrefix_bind_pure (dueEntriesAudit_erases _ _)
    | with_reducible exact auditFocus_erases (delTimerPrefix_erases _ _)
    | with_reducible exact auditFocus_erases (timerCallbackPrefix_erases _ _)
    | with_reducible apply runTimerSectionAudit_erases
    | with_reducible exact runCryptWorkersAudit_erases
    | with_reducible exact runSendWorkersAudit_erases
    | with_reducible exact runOneSendWorkerAudit_erases
    | with_reducible exact runOneClearWorkerAudit_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, reduceCtorEq, Std.TreeMap.get?_eq_getElem?]; all_goals try subst_vars; all_goals try contradiction)
    | (with_reducible intro x; try dsimp only)

theorem fireTimerAudit_erases (worker : Worker) (jHi : UInt64) :
    ErasesPrefix (fireTimerAudit worker jHi) (Env.fireTimer worker jHi) := by
  rw [← Environment.fireTimerSource_eq]
  unfold fireTimerAudit Environment.fireTimerSource
  cases ht : worker.timer? with
  | none => exact erasesPrefix_lift _
  | some t =>
    apply erasesPrefix_bind getDevSavedAudit_erases
    intro d
    exact erasesPrefix_bind_pure (duePeersAudit_erases d t jHi) (fireTimerAfterScanAudit_erases worker t jHi _)

theorem runTimersAudit_erases (jHi : UInt64) : ErasesPrefix (runTimersAudit jHi) (Env.runTimers jHi) := by
  unfold runTimersAudit Env.runTimers
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact getDevSavedAudit_erases
    | with_reducible apply erasesPrefix_bind_pure (duePeersAudit_erases _ _ _)
    | with_reducible apply erasesPrefix_bind_pure (dueEntriesAudit_erases _ _)
    | with_reducible exact auditFocus_erases (delTimerPrefix_erases _ _)
    | with_reducible exact auditFocus_erases (timerCallbackPrefix_erases _ _)
    | with_reducible apply runTimerSectionAudit_erases
    | with_reducible exact runCryptWorkersAudit_erases
    | with_reducible exact runSendWorkersAudit_erases
    | with_reducible exact runOneSendWorkerAudit_erases
    | with_reducible exact runOneClearWorkerAudit_erases
    | with_reducible exact fireTimerAudit_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, reduceCtorEq, Std.TreeMap.get?_eq_getElem?]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runTimersPlaceholderAudit_erases (jHi : UInt64) : ErasesPrefix (runTimersPlaceholderAudit jHi) (Env.runTimersPlaceholder jHi) := by
  rw [← Environment.runTimersPlaceholderSource_eq]
  unfold runTimersPlaceholderAudit Environment.runTimersPlaceholderSource
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact getDevSavedAudit_erases
    | with_reducible apply erasesPrefix_bind_pure (duePeersAudit_erases _ _ _)
    | with_reducible apply erasesPrefix_bind_pure (dueEntriesAudit_erases _ _)
    | with_reducible exact auditFocus_erases (delTimerPrefix_erases _ _)
    | with_reducible exact auditFocus_erases (timerCallbackPrefix_erases _ _)
    | with_reducible apply runTimerSectionAudit_erases
    | with_reducible exact runCryptWorkersAudit_erases
    | with_reducible exact runSendWorkersAudit_erases
    | with_reducible exact runOneSendWorkerAudit_erases
    | with_reducible exact runOneClearWorkerAudit_erases
    | with_reducible exact fireTimerAudit_erases _ _
    | with_reducible exact runTimersAudit_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, reduceCtorEq, Std.TreeMap.get?_eq_getElem?]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)


theorem idleTimersAudit_erases  : ErasesPrefix (idleTimersAudit) (Env.idleTimers) := by
  unfold idleTimersAudit Env.idleTimers
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact getDevSavedAudit_erases
    | with_reducible apply erasesPrefix_bind_pure (duePeersAudit_erases _ _ _)
    | with_reducible apply erasesPrefix_bind_pure (dueEntriesAudit_erases _ _)
    | with_reducible exact auditFocus_erases (delTimerPrefix_erases _ _)
    | with_reducible exact auditFocus_erases (timerCallbackPrefix_erases _ _)
    | with_reducible apply runTimerSectionAudit_erases
    | with_reducible exact runCryptWorkersAudit_erases
    | with_reducible exact runSendWorkersAudit_erases
    | with_reducible exact runOneSendWorkerAudit_erases
    | with_reducible exact runOneClearWorkerAudit_erases
    | with_reducible exact fireTimerAudit_erases _ _
    | with_reducible exact runTimersAudit_erases _
    | with_reducible exact runTimersPlaceholderAudit_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, reduceCtorEq, Std.TreeMap.get?_eq_getElem?]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem afterAdvanceAudit_erases  : ErasesPrefix (afterAdvanceAudit) (Env.afterAdvance) := by
  unfold afterAdvanceAudit Env.afterAdvance
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact getDevSavedAudit_erases
    | with_reducible apply erasesPrefix_bind_pure (duePeersAudit_erases _ _ _)
    | with_reducible apply erasesPrefix_bind_pure (dueEntriesAudit_erases _ _)
    | with_reducible exact auditFocus_erases (delTimerPrefix_erases _ _)
    | with_reducible exact auditFocus_erases (timerCallbackPrefix_erases _ _)
    | with_reducible apply runTimerSectionAudit_erases
    | with_reducible exact runCryptWorkersAudit_erases
    | with_reducible exact runSendWorkersAudit_erases
    | with_reducible exact runOneSendWorkerAudit_erases
    | with_reducible exact runOneClearWorkerAudit_erases
    | with_reducible exact fireTimerAudit_erases _ _
    | with_reducible exact runTimersAudit_erases _
    | with_reducible exact runTimersPlaceholderAudit_erases _
    | with_reducible exact idleTimersAudit_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, reduceCtorEq, Std.TreeMap.get?_eq_getElem?]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem fireTimerAfterScanAudit_preserves (worker : Worker) (t : PeerTimer) (jHi : UInt64) (due : List PeerId) :
    PrefixPreserves AuditInv AuditSafe (fireTimerAfterScanAudit worker t jHi due) := by
  unfold fireTimerAfterScanAudit
  simp only [bind_assoc, pure_bind]
  repeat' first
    | apply PrefixEnsures.bind getDevSavedAudit_spec
    | (apply PrefixEnsures.bind (duePeersAudit_spec _ _ _); intro due; change PrefixPreserves AuditInv AuditSafe _)
    | (apply PrefixEnsures.bind (dueEntriesAudit_spec _ _); intro due; change PrefixPreserves AuditInv AuditSafe _)
    | with_reducible exact auditFocus_preserves (AmbientContracts.drop (delTimerPrefix_spec allocationAmbient (fun _ => True) _ _))
    | exact auditFocus_preserves (timerCallbackPrefix_preserves allocationAmbient allocationTx allocationTimerQueue _ _)
    | with_reducible apply runTimerSectionAudit_preserves
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible exact runSendWorkersAudit_preserves
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact runOneClearWorkerAudit_preserves
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ peekNextSite_sameKernel
    | with_reducible exact auditLift_kernel _ (timerWorker_sameKernel _)
    | with_reducible exact auditLift_kernel _ (peekUnit_sameKernel _)
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ (peekSiteU64_sameKernel _)
    | with_reducible exact auditLift_kernel _ (hiddenJiffies_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, reduceCtorEq, Std.TreeMap.get?_eq_getElem?]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem fireTimerAudit_preserves (worker : Worker) (jHi : UInt64) :
    PrefixPreserves AuditInv AuditSafe (fireTimerAudit worker jHi) := by
  unfold fireTimerAudit
  cases ht : worker.timer? with
  | none => exact auditLift_kernel _ (by intro w x v hr; cases hr)
  | some t =>
    apply PrefixEnsures.preserves
    apply PrefixEnsures.bind getDevSavedAudit_spec
    intro d
    apply PrefixEnsures.bind (duePeersAudit_spec d t jHi)
    intro due
    exact fireTimerAfterScanAudit_preserves worker t jHi due

theorem runTimersAudit_preserves (jHi : UInt64) : PrefixPreserves AuditInv AuditSafe (runTimersAudit jHi) := by
  unfold runTimersAudit
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | apply PrefixEnsures.bind getDevSavedAudit_spec
    | (apply PrefixEnsures.bind (duePeersAudit_spec _ _ _); intro due; change PrefixPreserves AuditInv AuditSafe _)
    | (apply PrefixEnsures.bind (dueEntriesAudit_spec _ _); intro due; change PrefixPreserves AuditInv AuditSafe _)
    | with_reducible exact auditFocus_preserves (AmbientContracts.drop (delTimerPrefix_spec allocationAmbient (fun _ => True) _ _))
    | exact auditFocus_preserves (timerCallbackPrefix_preserves allocationAmbient allocationTx allocationTimerQueue _ _)
    | with_reducible apply runTimerSectionAudit_preserves
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible exact runSendWorkersAudit_preserves
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact runOneClearWorkerAudit_preserves
    | with_reducible exact fireTimerAudit_preserves _ _
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ peekNextSite_sameKernel
    | with_reducible exact auditLift_kernel _ (timerWorker_sameKernel _)
    | with_reducible exact auditLift_kernel _ (peekUnit_sameKernel _)
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ (peekSiteU64_sameKernel _)
    | with_reducible exact auditLift_kernel _ (hiddenJiffies_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, reduceCtorEq, Std.TreeMap.get?_eq_getElem?]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem runTimersPlaceholderAudit_preserves (jHi : UInt64) : PrefixPreserves AuditInv AuditSafe (runTimersPlaceholderAudit jHi) := by
  unfold runTimersPlaceholderAudit
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | apply PrefixEnsures.bind getDevSavedAudit_spec
    | (apply PrefixEnsures.bind (duePeersAudit_spec _ _ _); intro due; change PrefixPreserves AuditInv AuditSafe _)
    | (apply PrefixEnsures.bind (dueEntriesAudit_spec _ _); intro due; change PrefixPreserves AuditInv AuditSafe _)
    | with_reducible exact auditFocus_preserves (AmbientContracts.drop (delTimerPrefix_spec allocationAmbient (fun _ => True) _ _))
    | exact auditFocus_preserves (timerCallbackPrefix_preserves allocationAmbient allocationTx allocationTimerQueue _ _)
    | with_reducible apply runTimerSectionAudit_preserves
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible exact runSendWorkersAudit_preserves
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact runOneClearWorkerAudit_preserves
    | with_reducible exact fireTimerAudit_preserves _ _
    | with_reducible exact runTimersAudit_preserves _
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ peekNextSite_sameKernel
    | with_reducible exact auditLift_kernel _ (timerWorker_sameKernel _)
    | with_reducible exact auditLift_kernel _ (peekUnit_sameKernel _)
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ (peekSiteU64_sameKernel _)
    | with_reducible exact auditLift_kernel _ (hiddenJiffies_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, reduceCtorEq, Std.TreeMap.get?_eq_getElem?]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem idleTimersAudit_preserves  : PrefixPreserves AuditInv AuditSafe (idleTimersAudit) := by
  unfold idleTimersAudit
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | apply PrefixEnsures.bind getDevSavedAudit_spec
    | (apply PrefixEnsures.bind (duePeersAudit_spec _ _ _); intro due; change PrefixPreserves AuditInv AuditSafe _)
    | (apply PrefixEnsures.bind (dueEntriesAudit_spec _ _); intro due; change PrefixPreserves AuditInv AuditSafe _)
    | with_reducible exact auditFocus_preserves (AmbientContracts.drop (delTimerPrefix_spec allocationAmbient (fun _ => True) _ _))
    | exact auditFocus_preserves (timerCallbackPrefix_preserves allocationAmbient allocationTx allocationTimerQueue _ _)
    | with_reducible apply runTimerSectionAudit_preserves
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible exact runSendWorkersAudit_preserves
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact runOneClearWorkerAudit_preserves
    | with_reducible exact fireTimerAudit_preserves _ _
    | with_reducible exact runTimersAudit_preserves _
    | with_reducible exact runTimersPlaceholderAudit_preserves _
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ peekNextSite_sameKernel
    | with_reducible exact auditLift_kernel _ (timerWorker_sameKernel _)
    | with_reducible exact auditLift_kernel _ (peekUnit_sameKernel _)
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ (peekSiteU64_sameKernel _)
    | with_reducible exact auditLift_kernel _ (hiddenJiffies_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, reduceCtorEq, Std.TreeMap.get?_eq_getElem?]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem afterAdvanceAudit_preserves  : PrefixPreserves AuditInv AuditSafe (afterAdvanceAudit) := by
  unfold afterAdvanceAudit
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | apply PrefixEnsures.bind getDevSavedAudit_spec
    | (apply PrefixEnsures.bind (duePeersAudit_spec _ _ _); intro due; change PrefixPreserves AuditInv AuditSafe _)
    | (apply PrefixEnsures.bind (dueEntriesAudit_spec _ _); intro due; change PrefixPreserves AuditInv AuditSafe _)
    | with_reducible exact auditFocus_preserves (AmbientContracts.drop (delTimerPrefix_spec allocationAmbient (fun _ => True) _ _))
    | exact auditFocus_preserves (timerCallbackPrefix_preserves allocationAmbient allocationTx allocationTimerQueue _ _)
    | with_reducible apply runTimerSectionAudit_preserves
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible exact runSendWorkersAudit_preserves
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact runOneClearWorkerAudit_preserves
    | with_reducible exact fireTimerAudit_preserves _ _
    | with_reducible exact runTimersAudit_preserves _
    | with_reducible exact runTimersPlaceholderAudit_preserves _
    | with_reducible exact idleTimersAudit_preserves
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ peekNextSite_sameKernel
    | with_reducible exact auditLift_kernel _ (timerWorker_sameKernel _)
    | with_reducible exact auditLift_kernel _ (peekUnit_sameKernel _)
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ (peekSiteU64_sameKernel _)
    | with_reducible exact auditLift_kernel _ (hiddenJiffies_sameKernel _)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, reduceCtorEq, Std.TreeMap.get?_eq_getElem?]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem advanceAudit_erases (ticks : Nat) : ErasesPrefix (advanceAudit ticks) (Env.advance ticks) := erasesPrefix_lift _
theorem advanceAudit_preserves (ticks : Nat) : PrefixPreserves AuditInv AuditSafe (advanceAudit ticks) :=
  auditLift_kernel _ (advance_sameKernel ticks)

end Leanux.Proofs.WG.Lifetimes
