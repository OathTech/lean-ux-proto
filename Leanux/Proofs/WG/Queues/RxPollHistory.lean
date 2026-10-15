import Leanux.Proofs.WG.Queues.RxPollCaptureSupport
import Leanux.Proofs.WG.Lifetimes.Audit

/-! Persistent committed audit and poll metadata. Each poll starts a fresh local
GRO journal with exactly the current lifetime history, then appends its new
suffix. No observer is assumed independent of its incoming history. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

inductive Event where
  | audit (event : AuditEvent)
  | removed (occurrence : Nat) (skb : SkbId) (stamp : PacketStamp)
  | buffered (entry : RxJoint.Entry)
  | entered (entry : RxJoint.Entry)
  | completed (entry : RxJoint.Entry) (witness : RunWitness Unit)

def auditEvent : Event → Option AuditEvent | .audit e => some e | _ => none
def entryEvent : Event → Option RxJoint.Entry | .entered e => some e | _ => none
def auditHistory (h : List Event) := h.filterMap auditEvent
def entries (h : List Event) := h.filterMap entryEvent
def stamps (h : List Event) := (entries h).map RxJoint.Entry.stamp
def prior (h : List Event) := lifetimeHistory (auditHistory h)
def Released (h : List Event) (s : PacketStamp) := RxJoint.PriorReleased (prior h) s
abbrev Obs := PrefixM Event

def promote : RxJoint.Event → Event
  | .access e => .audit (.lifetime e)
  | .removed n skb s => .removed n skb s
  | .buffered e => .buffered e
  | .entered e => .entered e
  | .completed e r => .completed e r

theorem promote_audit (s : List RxJoint.Event) :
    auditHistory (s.map promote) = (s.filterMap RxJoint.accessEvent).map AuditEvent.lifetime := by
  unfold auditHistory
  induction s with
  | nil => rfl
  | cons e s ih => cases e <;> simp only [List.map_cons, List.filterMap_cons, promote, auditEvent, RxJoint.accessEvent, ih]

theorem promote_entries (s : List RxJoint.Event) :
    entries (s.map promote) = RxJoint.entries s := by
  unfold entries RxJoint.entries
  induction s with
  | nil => rfl
  | cons e s ih => cases e <;> simp only [List.map_cons, List.filterMap_cons, promote, entryEvent, RxJoint.enteredEntry, ih]

theorem promote_prior (s : List RxJoint.Event) : prior (s.map promote) = s.filterMap RxJoint.accessEvent := by
  rw [prior, promote_audit]
  exact filterMap_encoded AuditEvent.lifetime AuditEvent.lifetime? (fun _ => rfl) _

@[simp] theorem audit_append (h t : List Event) : auditHistory (h ++ t) = auditHistory h ++ auditHistory t :=
  List.filterMap_append
@[simp] theorem entries_append (h t : List Event) : entries (h ++ t) = entries h ++ entries t :=
  List.filterMap_append
@[simp] theorem prior_append (h t : List Event) : prior (h ++ t) = prior h ++ prior t := by
  simp only [prior, audit_append, lifetimeHistory, List.filterMap_append]
@[simp] theorem stamps_append (h t : List Event) : stamps (h ++ t) = stamps h ++ stamps t := by
  simp only [stamps, entries_append, List.map_append]

theorem released_append (h t : List Event) (s : PacketStamp) :
    Released (h ++ t) s ↔ Released h s ∨ Released t s := by
  simp only [Released, prior_append, RxJoint.PriorReleased, List.filterMap_append, AccessEvent.released_append]

def audit (a : AuditM α) : Obs α := focusPrefix Event.audit auditEvent a

theorem audit_erases (he : ErasesPrefix a original) : ErasesPrefix (audit a) original :=
  focusPrefix_erases _ _ he

theorem audit_entries (a : AuditM α) (w : World) (h : List Event) :
    entries (runPrefix (audit a) w h).2 = entries h :=
  focusPrefix_other Event.audit auditEvent entryEvent (fun _ => rfl) a w h

theorem audit_projects (ha : PrefixPreserves AuditInv AuditSafe a) :
    ProjectsUnder AuditInv auditEvent (audit a) a := ha.projects_focus _ _ (fun _ => rfl)

def observePoll (pid : PeerId) (budget : Nat) : Obs Nat :=
  fun w => ExceptT.mk fun h =>
    let initial := RxJoint.seed (prior h)
    let out := runPrefix (RxJoint.poll pid budget) w initial
    (out.1, h ++ (out.2.drop initial.length).map promote)

theorem observePoll_suffix (pid : PeerId) (budget : Nat) (w : World) (h : List Event)
    (out : Except Stop (Nat × World)) (suffix : List RxJoint.Event)
    (he : runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (prior h)) =
      (out, RxJoint.seed (prior h) ++ suffix)) :
    runPrefix (observePoll pid budget) w h = (out, h ++ suffix.map promote) := by
  change ((runPrefix (RxJoint.poll pid budget) w _).1,
    h ++ ((runPrefix (RxJoint.poll pid budget) w _).2.drop _).map _) = _
  rw [he]
  simp

theorem observePoll_appends (pid : PeerId) (budget : Nat) : Appends (observePoll pid budget) :=
  fun _ _ => ⟨_, rfl⟩

/-- Exact source result, successful World or Stop, for arbitrary input histories. -/
theorem observePoll_erases (pid : PeerId) (budget : Nat) :
    ErasesPrefix (observePoll pid budget)
      (rxPoll pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)) :=
  fun w h => RxJoint.poll_erases pid budget w (RxJoint.seed (prior h))

/-- Direct audit projection uses the identical incoming lifetime history in
both executions. Saved probes stay interleaved, and failed prefixes agree. -/
theorem observePoll_projects (pid : PeerId) (budget : Nat) :
    ProjectsUnder AuditInv auditEvent (observePoll pid budget)
      (auditFocus (rxPollStackPrefix pid budget)) := by
  intro w h hi
  obtain ⟨suffix, hs⟩ := RxJoint.poll_appends pid budget w (RxJoint.seed (prior h))
  have hl := RxJoint.poll_access pid budget w (RxJoint.seed (prior h))
    (by simpa only [RxJoint.seed_access, prior, auditHistory] using hi.1)
  rw [RxJoint.seed_access] at hl
  have lower : runPrefix (rxPollStackPrefix pid budget) w (prior h) =
      ((runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (prior h))).1,
        prior h ++ suffix.filterMap RxJoint.accessEvent) := by
    rw [hl, hs, List.filterMap_append, RxJoint.seed_access]
  have global := observePoll_suffix pid budget w h _ suffix (Prod.ext rfl hs)
  change runPrefix (auditFocus (rxPollStackPrefix pid budget)) w (auditHistory h) =
    ((runPrefix (observePoll pid budget) w h).1,
      auditHistory (runPrefix (observePoll pid budget) w h).2)
  rw [global]
  unfold auditFocus
  rw [focusPrefix_suffix AuditEvent.lifetime AuditEvent.lifetime? _ w (auditHistory h) _
    (suffix.filterMap RxJoint.accessEvent) lower]
  simp only [audit_append, promote_audit]

end Leanux.Proofs.WG.Queues.RxHistory
