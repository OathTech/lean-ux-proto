import Leanux.Kernel.Defs
/-! Recorded-list suffix relations and their composition. None is deliberately outside this recorded-input relation. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux

def Tail (records : List HiddenRecord) (remaining : Option (List HiddenRecord)) : Prop :=
  ∃ rest, remaining = some rest ∧ rest.IsSuffix records

def StrictTail (records : List HiddenRecord) (remaining : Option (List HiddenRecord)) : Prop :=
  ∃ rest, remaining = some rest ∧ rest.IsSuffix records ∧ rest.length < records.length

theorem tail_self (records : List HiddenRecord) : Tail records (some records) :=
  ⟨records,rfl,⟨[],rfl⟩⟩

theorem strict_tail {records : List HiddenRecord} {remaining : Option (List HiddenRecord)}
    (h : StrictTail records remaining) : Tail records remaining :=
  ⟨h.choose,h.choose_spec.1,h.choose_spec.2.1⟩

theorem tail_extend {records middle : List HiddenRecord} {remaining : Option (List HiddenRecord)}
    (prior : middle.IsSuffix records) (h : Tail middle remaining) : Tail records remaining := by
  obtain ⟨rest,stored,suffix⟩ := h
  exact ⟨rest,stored,suffix.trans prior⟩

theorem strict_extend {records middle : List HiddenRecord} {remaining : Option (List HiddenRecord)}
    (prior : middle.IsSuffix records) (h : StrictTail middle remaining) : StrictTail records remaining := by
  obtain ⟨rest,stored,suffix,shorter⟩ := h
  exact ⟨rest,stored,suffix.trans prior,Nat.lt_of_lt_of_le shorter prior.length_le⟩

theorem tail_after_strict {records middle : List HiddenRecord} {remaining : Option (List HiddenRecord)}
    (prior : middle.IsSuffix records) (shorter : middle.length < records.length)
    (h : Tail middle remaining) : StrictTail records remaining := by
  obtain ⟨rest,stored,suffix⟩ := h
  exact ⟨rest,stored,suffix.trans prior,Nat.lt_of_le_of_lt suffix.length_le shorter⟩
end Leanux.Proofs.WG.Progress.RecordSuffix
