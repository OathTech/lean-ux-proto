import Leanux.Proofs.WG.HandshakeSecurity.ResponderStackFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.Global
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

def consumer : RxHistory.Event → Option RxDisposition.ConsumeReceipt
  | .consumed _ _ _ r => some r
  | _ => none

def Checked (pre : List RxHistory.Event) : RxHistory.Event → Prop
  | .consumed _ _ _ r => History.Native (Confirmation.completedLabels pre) r.run.before
  | _ => True

def Safe (h : List RxHistory.Event) : Prop :=
  ∀ pre e post, h = pre ++ e :: post → Checked pre e

def Inv (h : List RxHistory.Event) (w : World) : Prop :=
  History.Native (Confirmation.completedLabels h) w.wg ∧ Safe h

abbrev Preserves (g : RxHistory.Obs α) := PrefixPreserves Inv Safe g

theorem Safe.append (old : Safe h)
    (new : ∀ pre e post, s = pre ++ e :: post → Checked (h ++ pre) e) : Safe (h ++ s) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h s old new

theorem Safe.quiet (old : Safe h) (empty : s.filterMap consumer = []) : Safe (h ++ s) := by
  apply old.append
  intro pre e post position
  cases e <;> try trivial
  case consumed occurrence id stamp r =>
    have member : RxHistory.Event.consumed occurrence id stamp r ∈ s := by rw [position]; simp
    have found : r ∈ s.filterMap consumer := List.mem_filterMap.mpr ⟨_, member, rfl⟩
    simp [empty] at found

theorem labels_consumer (h : List RxHistory.Event) :
    Confirmation.completedLabels h = (h.filterMap consumer).filterMap Confirmation.completedLabel := by
  rw [List.filterMap_filterMap]
  unfold Confirmation.completedLabels
  congr 1
  funext e
  cases e <;> rfl

theorem seed_labels (prior : List LifetimeEvent) : History.labels (RxJoint.seed prior) = [] := by
  rw [History.labels_consumer]
  unfold RxJoint.seed
  rw [filterMap_disjoint RxJoint.Event.access History.consumer (fun _ => rfl) prior]
  rfl

theorem seed_checks (base : List Nat) (prior : List LifetimeEvent) :
    History.Checks base (RxJoint.seed prior) := by
  have empty : (RxJoint.seed prior).filterMap History.consumer = [] :=
    filterMap_disjoint RxJoint.Event.access History.consumer (fun _ => rfl) prior
  have nilSafe : History.Checks base [] := by
    intro pre e post impossible
    cases pre <;> simp at impossible
  exact nilSafe.quiet empty

theorem promote_checks (h : List RxHistory.Event) (prior : List LifetimeEvent)
    (suffix : List RxJoint.Event) (old : Safe h)
    (localChecks : History.Checks (Confirmation.completedLabels h) (RxJoint.seed prior ++ suffix)) :
    Safe (h ++ suffix.map RxHistory.promote) := by
  apply old.append
  intro pre e post position
  obtain ⟨left, right, split, leftMap, rightMap⟩ := List.map_eq_append_iff.mp position
  obtain ⟨joint, tail, tailSplit, mapped, tailMap⟩ := List.map_eq_cons_iff.mp rightMap
  subst e
  have checked := localChecks (RxJoint.seed prior ++ left) joint tail
    (by rw [split, tailSplit]; simp only [List.append_assoc])
  cases joint <;> try trivial
  case consumed occurrence id stamp r =>
    change History.Native (Confirmation.completedLabels (h ++ pre)) r.run.before
    change History.Native (Confirmation.completedLabels h ++
      History.labels (RxJoint.seed prior ++ left)) r.run.before at checked
    rw [History.labels_append, seed_labels, List.nil_append] at checked
    rw [← leftMap, Confirmation.completedLabels, List.filterMap_append]
    rw [← Confirmation.completedLabels, ← Confirmation.completedLabels, History.labels_promote]
    exact checked

theorem observePoll (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges)
    (pid : PeerId) (budget : Nat) : Preserves (RxHistory.observePoll pid budget) := by
  intro w h hi
  have entry : History.State (Confirmation.completedLabels h) (RxJoint.seed (RxHistory.prior h)) w :=
    ⟨by simpa only [seed_labels, List.append_nil] using hi.1, seed_checks _ _⟩
  obtain ⟨suffix, appends, safe, normal⟩ :=
    History.poll H1 slots deliverInner_native pid budget _ w _ entry
  have global := RxHistory.observePoll_suffix pid budget w h _ suffix (Prod.ext rfl appends)
  have checked : Safe (h ++ suffix.map RxHistory.promote) :=
    promote_checks h _ suffix hi.2 (by simpa only [appends] using safe)
  refine ⟨suffix.map RxHistory.promote, congrArg Prod.snd global, ?_, ?_⟩
  · simpa only [global] using checked
  · rw [global]
    cases run : (runPrefix (RxJoint.poll pid budget) w (RxJoint.seed (RxHistory.prior h))).1 with
    | error stop => trivial
    | ok out =>
      simp only [run] at normal
      refine ⟨?_, checked⟩
      change History.Native (Confirmation.completedLabels (h ++ suffix.map RxHistory.promote)) out.2.wg
      have state := normal.1
      rw [appends, History.labels_append, seed_labels, List.nil_append] at state
      rw [Confirmation.completedLabels, List.filterMap_append,
        ← Confirmation.completedLabels, ← Confirmation.completedLabels, History.labels_promote]
      exact state

/-- The global observer invariant starts at both real fixture variants.
This initialization fact does not itself supply outer runner preservation. -/
theorem initial (net bare : Bool) (w : World)
    (same : wgStoreView w.wg = wgStoreView (Runner.initialWG net bare)) : Inv [] w := by
  have device : w.wg.dev = (Runner.initialWG net bare).dev := congrArg WGStoreView.dev same
  have root := History.Native.initial net bare
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply Authorized.frame root.1
    unfold current
    rw [device]
  · apply CurrentSlots.fields_transport root.2
    unfold CurrentSlots.fields RxCredits.keyWords
    rw [device]
  · intro pre e post impossible
    cases pre <;> simp at impossible

end Leanux.Proofs.WG.HandshakeSecurity.Responder.Global
