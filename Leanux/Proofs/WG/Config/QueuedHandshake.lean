import Leanux.Proofs.WG.Config.QueuedReferenceSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def queuedAfterClock (pid : PeerId) (p : Peer) (now : Int64) : WG.M Unit := do
  let lhs := p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64
  if ← branchCmp .queuedNotExpired (!(lhs ≤ now)) lhs.toInt now.toInt then return
  if ← branch .queuedDead p.isDead then return
  peerGet pid
  if ← branch .queuedAlreadyQueued (p.handshakePending && !(← peekQueuedUnit .sendWorker pid)) then
    peerPut (some pid)
    return
  setPeer pid { (← getPeer pid) with handshakePending := true }
  recordQueued .sendWorker pid
  modifyDev fun d => { d with sendWorkQueue := d.sendWorkQueue ++ [pid] }

def queuedReadPrefix (pid : PeerId) : WG.M Peer := do
  requireNotPending pid "queueing a handshake"
  if ← branch .queuedNotRetry true then
    setPeer pid { (← getPeer pid) with timerHandshakeAttempts := 0 }
  getPeer pid

theorem sendQueued_clock_factor (pid : PeerId) :
    sendQueuedHandshakeInitiation pid false = (do
      let p ← queuedReadPrefix pid
      let now ← hiddenClock64 .birthdateExpired
      queuedAfterClock pid p now) := by
  simp [sendQueuedHandshakeInitiation, queuedReadPrefix, queuedAfterClock,
    requireNotPending, branchExpired, birthdateTest, branch, AmbientM.branch, bind_assoc]

theorem queuedReadPrefix_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (queuedReadPrefix pid) (fun w => w.dev = some d)
      (fun result w => result = { p with timerHandshakeAttempts := 0 } ∧
        w.dev = some (withPeer d pid { p with timerHandshakeAttempts := 0 })) := by
  intro g ambient device
  refine ⟨{p with timerHandshakeAttempts := 0},
    {g with dev := some (withPeer d pid {p with timerHandshakeAttempts := 0})},
    {ambient with steps := ambient.steps.push {decision := .queuedNotRetry, outcome := true, netRx := ambient.netRxSection}}, ?_, rfl, rfl⟩
  simp [queuedReadPrefix, requireNotPending, branch, AmbientM.branch,
    getPeer, getDev, device, resident, setPeer, modifyDev, withPeer]
  rfl


/-- The actual suffix, decorated only with the result of its real queue-record inspection. -/
def observedQueuedAfterClock (pid : PeerId) (p : Peer) (now : Int64) : WG.M (Option Bool) := do
  let lhs := p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64
  if ← branchCmp .queuedNotExpired (!(lhs ≤ now)) lhs.toInt now.toInt then return none
  if ← branch .queuedDead p.isDead then return none
  peerGet pid
  let queued ← peekQueuedUnit .sendWorker pid
  if ← branch .queuedAlreadyQueued (p.handshakePending && !queued) then
    peerPut (some pid)
    return some queued
  setPeer pid { (← getPeer pid) with handshakePending := true }
  recordQueued .sendWorker pid
  modifyDev fun d => { d with sendWorkQueue := d.sendWorkQueue ++ [pid] }
  return some queued

theorem observedQueuedAfterClock_erase (pid : PeerId) (p : Peer) (now : Int64) :
    (do let _ ← observedQueuedAfterClock pid p now; pure ()) = queuedAfterClock pid p now := by
  have cond {α β : Type} (q : Prop) [Decidable q] (a b : WG.M α) (f : α → WG.M β) :
      ((if q then a else b) >>= f) = (if q then a >>= f else b >>= f) := by split <;> rfl
  simp only [observedQueuedAfterClock, queuedAfterClock, bind_assoc, cond, pure_bind]
  congr 1

/-- Current prediction includes the actual queue-record inspection. -/
def queuedDeviceAfterInspection (d : Device) (pid : PeerId) (p : Peer) (now : Int64) (queued : Bool) : Device :=
  if !(p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now) || p.isDead then d
  else
    let acquired := withPeer d pid {p with refcount := p.refcount + 1}
    if p.handshakePending && !queued then
      withPeer acquired pid p
    else
      let pending := withPeer acquired pid {p with refcount := p.refcount + 1, handshakePending := true}
      {pending with sendWorkQueue := pending.sendWorkQueue ++ [pid]}


/-- Corrected effect, indexed by the bit returned by the actual inspection. -/
theorem queuedAfterClock_exact (pid : PeerId) (d : Device) (p : Peer) (now : Int64)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (observedQueuedAfterClock pid p now) (fun s => s.wg.device = some d)
      (fun seen s => match seen with
        | none => s.wg.device = some d ∧
            (¬p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now ∨ p.isDead = true)
        | some queued => p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now ∧
            p.isDead = false ∧ s.wg.device = some (queuedDeviceAfterInspection d pid p now queued)) := by
  let Q : Option Bool → WGWorld → Prop := fun seen g => match seen with
    | none => g.dev = some d ∧
        (¬p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now ∨ p.isDead = true)
    | some queued => p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now ∧
        p.isDead = false ∧ g.dev = some (queuedDeviceAfterInspection d pid p now queued)
  change Ensures _ (fun g => g.dev = some d) Q
  have branchBind {α : Type} (site : Decision) (value : Bool) (next : Bool → WG.M α)
      (P : WGWorld → Prop) (R : α → WGWorld → Prop) (rest : Ensures (next value) P R) :
      Ensures (branch site value >>= next) P R := by
    intro g ambient result final after pre run
    change ((next value).run g).run _ = _ at run
    exact rest g _ result final after pre run
  have compareBind {α : Type} (site : Decision) (value : Bool) (lhs rhs : Int)
      (next : Bool → WG.M α) (P : WGWorld → Prop) (R : α → WGWorld → Prop)
      (rest : Ensures (next value) P R) :
      Ensures (branchCmp site value lhs rhs >>= next) P R := by
    intro g ambient result final after pre run
    change ((next value).run g).run _ = _ at run
    exact rest g _ result final after pre run
  unfold observedQueuedAfterClock
  refine compareBind _ _ _ _ _ _ _ ?_
  by_cases expired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now
  · simp only [expired, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    refine branchBind _ _ _ _ _ ?_
    cases dead : p.isDead with
    | true =>
      simp only [ite_true]
      intro g ambient result final after device run
      cases run
      exact ⟨device, Or.inr dead⟩
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (peerGet_exact pid d p resident)) ?_
      intro ignored
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
        (AmbientM.peekQueuedUnit .sendWorker pid)
        (fun g : WGWorld => g.dev = some (withPeer d pid {p with refcount := p.refcount + 1}) ∧ 0 < p.refcount))) ?_
      intro queued
      refine branchBind _ _ _ _ _ ?_
      cases refused : (p.handshakePending && !queued) with
      | true =>
        simp only [ite_true]
        have put : Ensures (peerPut (some pid))
            (fun g : WGWorld => g.dev = some (withPeer d pid {p with refcount := p.refcount + 1}) ∧ 0 < p.refcount)
            (fun _ g => g.dev = some (withPeer (withPeer d pid {p with refcount := p.refcount + 1}) pid p)) := by
          intro g ambient result final after pre run
          have hp := (ensures_iff _ _ _).mpr (peerPut_retained pid
            (withPeer d pid {p with refcount := p.refcount + 1})
            {p with refcount := p.refcount + 1} (by simp [withPeer]) (by simp; omega))
            g ambient result final after pre.1 run
          simpa only [Nat.add_sub_cancel] using hp
        refine ensures_bind _ _ put ?_
        intro ignored g ambient result final after device run
        cases run
        exact ⟨expired, dead, by simpa [queuedDeviceAfterInspection, expired, dead, refused] using device⟩
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        let pending := withPeer (withPeer d pid {p with refcount := p.refcount + 1}) pid
          {p with refcount := p.refcount + 1, handshakePending := true}
        have setPending : Ensures (do setPeer pid {(← getPeer pid) with handshakePending := true})
            (fun g : WGWorld => g.dev = some (withPeer d pid {p with refcount := p.refcount + 1}) ∧ 0 < p.refcount)
            (fun _ g => g.dev = some pending) := by
          intro g ambient result final after pre run
          simp [getPeer, getDev, pre.1, withPeer, setPeer, modifyDev] at run
          rcases run with ⟨rfl, rfl⟩
          rfl
        have factor : (do
            let peer ← getPeer pid
            setPeer pid {peer with handshakePending := true}
            recordQueued .sendWorker pid
            modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}
            pure (some queued)) = (do
            (do setPeer pid {(← getPeer pid) with handshakePending := true})
            recordQueued .sendWorker pid
            modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}
            pure (some queued) : WG.M (Option Bool)) := by simp only [bind_assoc]
        rw [factor]
        refine ensures_bind _ _ setPending ?_
        intro ignored
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
          (hoare_liftAmbient_variant (AmbientM.recordQueued .sendWorker pid)
            (fun g : WGWorld => g.dev = some pending))) ?_
        intro ignored g ambient result final after device run
        simp [modifyDev, device] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        exact ⟨expired, dead, by simp [queuedDeviceAfterInspection, expired, dead, refused, pending]⟩
  · simp only [expired, decide_false, Bool.not_false, ite_true]
    intro g ambient result final after device run
    cases run
    exact ⟨device, Or.inl expired⟩


/-- Decorate the actual clock and queue-record decision of one full call. -/
def observedSendQueued (pid : PeerId) : WG.M (Int64 × Option Bool) := do
  let p ← queuedReadPrefix pid
  let now ← hiddenClock64 .birthdateExpired
  let seen ← observedQueuedAfterClock pid p now
  pure (now, seen)

theorem observedSendQueued_erase (pid : PeerId) :
    (do let _ ← observedSendQueued pid; pure ()) = sendQueuedHandshakeInitiation pid false := by
  rw [sendQueued_clock_factor]
  simp only [observedSendQueued, bind_assoc, pure_bind]
  congr 1
  funext p
  congr 1
  funext now
  exact observedQueuedAfterClock_erase pid p now

/-- The witnesses are executions of the actual prefix, clock and decorated suffix. -/
theorem sendQueued_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (g final : WGWorld) (ambient ending : Ambient) (device : g.dev = some d)
    (run : ((sendQueuedHandshakeInitiation pid false).run g).run ambient = .ok (((), final), ending)) :
    ∃ now seen before beforeAmbient afterClock clockAmbient,
      ((queuedReadPrefix pid).run g).run ambient =
        .ok (({p with timerHandshakeAttempts := 0}, before), beforeAmbient) ∧
      ((hiddenClock64 .birthdateExpired : WG.M Int64).run before).run beforeAmbient =
        .ok ((now, afterClock), clockAmbient) ∧
      ((observedQueuedAfterClock pid {p with timerHandshakeAttempts := 0} now).run afterClock).run clockAmbient =
        .ok ((seen, final), ending) ∧
      match seen with
      | none => final.dev = some (withPeer d pid {p with timerHandshakeAttempts := 0}) ∧
          (¬p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now ∨ p.isDead = true)
      | some queued => p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now ∧
          p.isDead = false ∧ final.dev = some (queuedDeviceAfterInspection
            (withPeer d pid {p with timerHandshakeAttempts := 0}) pid {p with timerHandshakeAttempts := 0} now queued) := by
  obtain ⟨value, before, beforeAmbient, prefixRun, rfl, beforeDevice⟩ :=
    queuedReadPrefix_returns pid d p resident g ambient device
  have bindRun {α β : Type} (action : WG.M α) (next : α → WG.M β)
      (state : WGWorld) (input : Ambient) :
      (((action >>= next).run state).run input) =
        (((action.run state).run input) >>= fun ((value, middle), remaining) =>
          ((next value).run middle).run remaining) := rfl
  have okBind {α β : Type} (value : α) (next : α → Except Stop β) :
      (Except.ok value >>= next) = next value := rfl
  rw [sendQueued_clock_factor] at run
  simp only [bindRun, prefixRun, okBind] at run
  cases clockRun : ((hiddenClock64 .birthdateExpired : WG.M Int64).run before).run beforeAmbient with
  | error stop => rw [clockRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨now, afterClock⟩, clockAmbient⟩ := pair
    rw [clockRun] at run
    simp only [okBind] at run
    have clockDevice := (ensures_iff _ _ _).mpr
      (hoare_liftAmbient_variant (AmbientM.hiddenClock64 .birthdateExpired)
        (fun g : WGWorld => g.dev = some (withPeer d pid {p with timerHandshakeAttempts := 0})))
      before beforeAmbient now afterClock clockAmbient beforeDevice clockRun
    rw [← observedQueuedAfterClock_erase] at run
    simp only [bindRun] at run
    cases observedRun : ((observedQueuedAfterClock pid {p with timerHandshakeAttempts := 0} now).run afterClock).run clockAmbient with
    | error stop => rw [observedRun] at run; cases run
    | ok pair =>
      obtain ⟨⟨seen, complete⟩, after⟩ := pair
      rw [observedRun] at run
      cases run
      refine ⟨now, seen, before, beforeAmbient, afterClock, clockAmbient, prefixRun, clockRun, observedRun, ?_⟩
      exact queuedAfterClock_exact pid (withPeer d pid {p with timerHandshakeAttempts := 0})
        {p with timerHandshakeAttempts := 0} now (by simp [withPeer])
        afterClock clockAmbient seen complete after clockDevice observedRun

/-- Corrected projected result: the returned clock and inspection bit belong
    to this actual decorated call, whose erasure is the original operation. -/
theorem sendQueued_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (observedSendQueued pid) (fun s => s.wg.device = some d)
      (fun result s => match result.2 with
        | none => s.wg.device = some (withPeer d pid {p with timerHandshakeAttempts := 0}) ∧
            (¬p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ result.1 ∨ p.isDead = true)
        | some queued => p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ result.1 ∧
            p.isDead = false ∧ s.wg.device = some (queuedDeviceAfterInspection
              (withPeer d pid {p with timerHandshakeAttempts := 0}) pid
                {p with timerHandshakeAttempts := 0} result.1 queued)) := by
  intro g ambient result final ending device run
  change g.dev = some d at device
  obtain ⟨value, before, beforeAmbient, prefixRun, rfl, beforeDevice⟩ :=
    queuedReadPrefix_returns pid d p resident g ambient device
  have bindRun {α β : Type} (action : WG.M α) (next : α → WG.M β)
      (state : WGWorld) (input : Ambient) :
      (((action >>= next).run state).run input) =
        (((action.run state).run input) >>= fun ((value, middle), remaining) =>
          ((next value).run middle).run remaining) := rfl
  have okBind {α β : Type} (value : α) (next : α → Except Stop β) :
      (Except.ok value >>= next) = next value := rfl
  simp only [observedSendQueued, bindRun, prefixRun, okBind] at run
  cases clockRun : ((hiddenClock64 .birthdateExpired : WG.M Int64).run before).run beforeAmbient with
  | error stop => rw [clockRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨now, afterClock⟩, clockAmbient⟩ := pair
    rw [clockRun] at run
    simp only [okBind] at run
    have clockDevice := (ensures_iff _ _ _).mpr
      (hoare_liftAmbient_variant (AmbientM.hiddenClock64 .birthdateExpired)
        (fun g : WGWorld => g.dev = some (withPeer d pid {p with timerHandshakeAttempts := 0})))
      before beforeAmbient now afterClock clockAmbient beforeDevice clockRun
    cases observedRun : ((observedQueuedAfterClock pid {p with timerHandshakeAttempts := 0} now).run afterClock).run clockAmbient with
    | error stop => rw [observedRun] at run; cases run
    | ok pair =>
      obtain ⟨⟨seen, complete⟩, after⟩ := pair
      rw [observedRun] at run
      cases run
      exact queuedAfterClock_exact pid (withPeer d pid {p with timerHandshakeAttempts := 0})
        {p with timerHandshakeAttempts := 0} now (by simp [withPeer])
        afterClock clockAmbient seen complete after clockDevice observedRun

/-- Historical prediction retained for unported callers; refuted by the queued-handshake finding. -/
def queuedDevice (d : Device) (pid : PeerId) (p : Peer) (now : Int64) : Device :=
  if !(p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now) || p.isDead then d
  else
    let acquired := withPeer d pid { p with refcount := p.refcount + 1 }
    if p.handshakePending then
      withPeer acquired pid p
    else
      let pending := withPeer acquired pid { p with refcount := p.refcount + 1, handshakePending := true }
      { pending with sendWorkQueue := pending.sendWorkQueue ++ [pid] }

end Leanux.Proofs.WG.Config
