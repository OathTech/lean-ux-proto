import Leanux.Proofs.WG.HandshakeSecurity.ResponderLabels

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.History
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

/-- The live state obligation carried at normal actor boundaries. Bounds prevent
session allocation from replacing a currently selected old slot. -/
def Native (confirmed : List Nat) (w : WGWorld) : Prop :=
  Authorized confirmed w ∧ CurrentSlots.Inv w

def consumer : RxJoint.Event → Option RxDisposition.ConsumeReceipt
  | .consumed _ _ _ r => some r
  | _ => none

def label (e : RxJoint.Event) : Option Nat := (consumer e).bind Confirmation.completedLabel

def labels (h : List RxJoint.Event) : List Nat := h.filterMap label

def Checked (base : List Nat) (pre : List RxJoint.Event) : RxJoint.Event → Prop
  | .consumed _ _ _ r => Native (base ++ labels pre) r.run.before
  | _ => True

def Checks (base : List Nat) (h : List RxJoint.Event) : Prop :=
  ∀ pre e post, h = pre ++ e :: post → Checked base pre e

def State (base : List Nat) (h : List RxJoint.Event) (w : World) : Prop :=
  Native (base ++ labels h) w.wg ∧ Checks base h

theorem Native.initial (net bare : Bool) : Native [] (Runner.initialWG net bare) :=
  ⟨Responder.initial net bare, CurrentSlots.initial net bare _ rfl⟩

theorem labels_consumer (h : List RxJoint.Event) :
    labels h = (h.filterMap consumer).filterMap Confirmation.completedLabel := by
  rw [List.filterMap_filterMap]
  rfl

theorem labels_append (a b : List RxJoint.Event) : labels (a ++ b) = labels a ++ labels b :=
  List.filterMap_append

theorem labels_consumed (n id : Nat) (stamp : PacketStamp) (r : RxDisposition.ConsumeReceipt) :
    labels [.consumed n id stamp r] = (Confirmation.completedLabel r).toList := by
  cases label : Confirmation.completedLabel r <;> simp [labels, History.label, consumer, label]

theorem labels_buffered (entry : RxJoint.Entry) : labels [.buffered entry] = [] := rfl

theorem labels_promote (h : List RxJoint.Event) :
    Confirmation.completedLabels (h.map RxHistory.promote) = labels h := by
  induction h with
  | nil => rfl
  | cons e es ih =>
    cases e <;> simp only [Confirmation.completedLabels, labels, List.map_cons,
      List.filterMap_cons, RxHistory.promote, Confirmation.eventLabel, label, consumer,
      Option.bind_none, Option.bind_some] at ih ⊢ <;> rw [ih]

theorem Checks.append (old : Checks base h)
    (new : ∀ pre e post, s = pre ++ e :: post → Checked base (h ++ pre) e) :
    Checks base (h ++ s) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    (Checked base) h s old new

theorem Checks.snoc (old : Checks base h) (new : Checked base h e) : Checks base (h ++ [e]) := by
  apply old.append
  intro pre x post position
  cases pre with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at position
    obtain ⟨rfl, _⟩ := position
    simpa using new
  | cons y ys => cases ys <;> simp at position

theorem checked_quiet (quiet : consumer e = none) : Checked base pre e := by
  cases e <;> trivial

theorem Checks.quiet (old : Checks base h) (empty : s.filterMap consumer = []) :
    Checks base (h ++ s) := by
  apply old.append
  intro pre e post position
  apply checked_quiet
  have member : e ∈ s := by rw [position]; simp
  cases result : consumer e with
  | none => rfl
  | some r =>
    have found : r ∈ s.filterMap consumer := List.mem_filterMap.mpr ⟨e, member, result⟩
    simp [empty] at found


end Leanux.Proofs.WG.HandshakeSecurity.Responder.History
