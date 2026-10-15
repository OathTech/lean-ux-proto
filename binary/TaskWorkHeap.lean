import TaskLayouts
import FdHeap

namespace Binary.TaskWorkHeap
open Leanux
abbrev Address := BitVec 64
open FdHeap (Word)

/-- Classification retains every callback. An `other` callback is not a
    claim about its effects, and cannot be classified as `____fput`. -/
inductive Work where
  | fput (file : FileId)
  | other (node function : Address)
  deriving DecidableEq

def Work.node (files : FileId → Address) : Work → Address
  | .fput id => files id + .ofNat 64 TaskLayouts.file_f_task_work
  | .other node _ => node

def Work.function : Work → Address
  | .fput _ => TaskLayouts.fputCallbackAddress
  | .other _ function => function

def Work.Valid (relevant : FileId → Prop) : Work → Prop
  | .fput id => relevant id
  | .other _ function => function ≠ TaskLayouts.fputCallbackAddress

def fputs (works : List Work) : List FileId :=
  works.filterMap (fun work => match work with | .fput id => some id | .other _ _ => none)

theorem Work.unique {relevant} (names : FdHeap.Names relevant) {first second : Work}
    (hf : first.Valid relevant) (hs : second.Valid relevant)
    (nodes : first.node names.address = second.node names.address)
    (functions : first.function = second.function) : first = second := by
  cases first with
  | fput id =>
    cases second with
    | fput other =>
      have addresses : names.address id = names.address other := by
        have equal := congrArg (fun x : Address => x - .ofNat 64 TaskLayouts.file_f_task_work) nodes
        simpa only [Work.node, BitVec.add_sub_cancel] using equal
      exact congrArg Work.fput (names.unique id other hf hs addresses)
    | other node function => exact False.elim (hs functions.symm)
  | other node function =>
    cases second with
    | fput id => exact False.elim (hf functions)
    | other other funOther =>
      change node = other at nodes
      change function = funOther at functions
      subst other
      subst funOther
      rfl

/-- Finite physical callback chain. NULL terminates it; work_exited is a
    distinct closed-queue marker, never a callback. Every next and function
    word is read, including callbacks outside the fput projection. -/
def Chain (memory : Mem 64) (files : FileId → Address) (relevant : FileId → Prop) :
    Address → List Work → Prop
  | cursor, [] => cursor = 0
  | cursor, work :: rest =>
      cursor = work.node files ∧ cursor ≠ 0 ∧ cursor ≠ TaskLayouts.workExitedAddress ∧
      work.Valid relevant ∧
      Word memory (cursor + .ofNat 64 TaskLayouts.callback_func) work.function ∧
      ∃ next, Word memory (cursor + .ofNat 64 TaskLayouts.callback_next) next ∧
        Chain memory files relevant next rest

def Reads (files : FileId → Address) (works : List Work) (address : Address) : Prop :=
  ∃ work ∈ works,
    InRange (work.node files + .ofNat 64 TaskLayouts.callback_next) 8 address ∨
    InRange (work.node files + .ofNat 64 TaskLayouts.callback_func) 8 address

theorem Chain.functional {relevant memory cursor first second}
    (names : FdHeap.Names relevant)
    (hf : Chain memory names.address relevant cursor first)
    (hs : Chain memory names.address relevant cursor second) : first = second := by
  induction first generalizing cursor second with
  | nil =>
    cases second with
    | nil => rfl
    | cons work rest => exact False.elim (hs.2.1 hf)
  | cons work rest ih =>
    cases second with
    | nil => exact False.elim (hf.2.1 hs)
    | cons other tail =>
      obtain ⟨nodeF, _, _, validF, functionF, nextF, loadF, chainF⟩ := hf
      obtain ⟨nodeS, _, _, validS, functionS, nextS, loadS, chainS⟩ := hs
      have equal := Work.unique names validF validS (nodeF.symm.trans nodeS)
        (functionF.functional functionS)
      have next := loadF.functional loadS
      subst nextS
      rw [equal, ih chainF chainS]

theorem Chain.frame {before after files relevant cursor works writes}
    (same : EqualOutside writes before after)
    (apart : ∀ address, Reads files works address → ¬writes address)
    (represented : Chain before files relevant cursor works) :
    Chain after files relevant cursor works := by
  induction works generalizing cursor with
  | nil => exact represented
  | cons work rest ih =>
    obtain ⟨node, nonnull, notExited, valid, function, next, loaded, tail⟩ := represented
    refine ⟨node, nonnull, notExited, valid, ?_, next, ?_, ?_⟩
    · apply function.frame same
      intro i hi
      apply apart _
      exact ⟨work, by simp, .inr (node ▸ ⟨i, hi, rfl⟩)⟩
    · apply loaded.frame same
      intro i hi
      apply apart _
      exact ⟨work, by simp, .inl (node ▸ ⟨i, hi, rfl⟩)⟩
    · apply ih _ tail
      intro address read
      obtain ⟨cell, member, read⟩ := read
      exact apart address ⟨cell, List.mem_cons_of_mem _ member, read⟩

/-- Only the queue still attached to task_struct. A task_work_run activation
    may have a detached batch in addition; this predicate does not invent one. -/
def Queued (memory : Mem 64) (task : Address) (files : FileId → Address)
    (relevant : FileId → Prop) (works : List Work) : Prop :=
  ∃ first, Word memory (task + .ofNat 64 TaskLayouts.task_task_works) first ∧
    Chain memory files relevant first works

def Closed (memory : Mem 64) (task : Address) : Prop :=
  Word memory (task + .ofNat 64 TaskLayouts.task_task_works) TaskLayouts.workExitedAddress

theorem Queued.functional {relevant memory task first second}
    (names : FdHeap.Names relevant)
    (hf : Queued memory task names.address relevant first)
    (hs : Queued memory task names.address relevant second) : first = second := by
  obtain ⟨nodeF, loadF, chainF⟩ := hf
  obtain ⟨nodeS, loadS, chainS⟩ := hs
  have equal := loadF.functional loadS
  subst nodeS
  exact chainF.functional names chainS

theorem Queued.not_closed {memory task files relevant works}
    (queued : Queued memory task files relevant works) : ¬Closed memory task := by
  intro closed
  obtain ⟨first, loaded, chain⟩ := queued
  have equal := loaded.functional closed
  cases works with
  | nil =>
    have nonzero : TaskLayouts.workExitedAddress ≠ 0 := by decide
    exact nonzero (equal.symm.trans chain)
  | cons work rest => exact chain.2.2.1 equal

theorem Queued.frame {before after task files relevant works writes}
    (same : EqualOutside writes before after)
    (headApart : ∀ i < 8, ¬writes (task + .ofNat 64 TaskLayouts.task_task_works + .ofNat 64 i))
    (chainApart : ∀ address, Reads files works address → ¬writes address)
    (represented : Queued before task files relevant works) :
    Queued after task files relevant works := by
  obtain ⟨first, loaded, chain⟩ := represented
  exact ⟨first, loaded.frame same headApart, chain.frame same chainApart⟩

theorem Closed.frame {before after task writes}
    (same : EqualOutside writes before after)
    (apart : ∀ i < 8, ¬writes (task + .ofNat 64 TaskLayouts.task_task_works + .ofNat 64 i))
    (represented : Closed before task) : Closed after task := Word.frame same apart represented

/-- Projection preserves physical order. This equality does not license
    ignoring other callbacks' effects or assuming that they cannot enqueue. -/
theorem fputs_append (first second : List Work) :
    fputs (first ++ second) = fputs first ++ fputs second := by
  simp only [fputs, List.filterMap_append]

#print axioms Work.unique
#print axioms Chain.functional
#print axioms Chain.frame
#print axioms Queued.functional
#print axioms Queued.not_closed
#print axioms Queued.frame
#print axioms Closed.frame
#print axioms fputs_append
end Binary.TaskWorkHeap
