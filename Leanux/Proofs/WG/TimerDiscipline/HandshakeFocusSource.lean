import Leanux.Proofs.WG.TimerDiscipline.HandshakeJournalClaims
import Leanux.Proofs.WG.TimerDiscipline.HookDerivedFrames
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem ValidHistory.decoded {h : List Event} (valid : ValidHistory h) :
    HookJournal.ValidHistory (h.filterMap decodeHook) := by
  intro r member
  obtain ⟨e,mem,eq⟩:=List.mem_filterMap.mp member
  cases e with
  | session _ => cases eq
  | hook q =>
    cases eq
    exact valid (.hook r) mem

theorem ValidHistory.append_hooks {h : List Event} (prior : ValidHistory h)
    {suffix : List HookJournal.Receipt} (fresh : HookJournal.ValidHistory suffix) :
    ValidHistory (h++suffix.map Event.hook) := by
  intro e member
  rcases List.mem_append.mp member with old | new
  · exact prior e old
  · obtain ⟨r,mem,rfl⟩:=List.mem_map.mp new
    exact fresh r mem

theorem Paired.append_hooks {h : List Event} (prior : Paired h)
    {suffix : List HookJournal.Receipt}
    (quiet : ∀r∈suffix,r.hook≠.sessionDerived) : Paired (h++suffix.map Event.hook) := by
  induction suffix generalizing h with
  | nil => simpa using prior
  | cons r rs ih =>
    have first:=Paired.quiet r prior (quiet r (by simp))
    have rest:=ih first (fun q mem=>quiet q (by simp [mem]))
    simpa only [List.map_cons,List.append_assoc,List.cons_append,List.nil_append] using rest

theorem focus_valid {State α : Type} {g : PrefixT HookJournal.Receipt State α}
    (keeps : PrefixPreserves (fun h _=>HookJournal.ValidHistory h) HookJournal.ValidHistory g) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory
      (focusPrefix Event.hook decodeHook g) := by
  intro w h prior
  obtain ⟨suffix,he,valid,_⟩:=keeps w (h.filterMap decodeHook) prior.decoded
  have eq : runPrefix g w (h.filterMap decodeHook) =
      ((runPrefix g w (h.filterMap decodeHook)).1,h.filterMap decodeHook++suffix) :=
    Prod.ext rfl he
  rw [focusPrefix_suffix Event.hook decodeHook g w h _ suffix eq]
  have fresh : HookJournal.ValidHistory suffix := by
    intro r member
    apply valid r
    rw [he]
    exact List.mem_append_right _ member
  have next:=prior.append_hooks fresh
  refine ⟨suffix.map Event.hook,rfl,next,?_⟩
  cases (runPrefix g w (h.filterMap decodeHook)).1 <;> trivial

theorem focus_paired {State α : Type} {g : PrefixT HookJournal.Receipt State α}
    (appends : Appends g) (frame : HistoryFrame HookJournal.derivedReceipt g) :
    PrefixPreserves (fun h _=>Paired h) Paired (focusPrefix Event.hook decodeHook g) := by
  intro w h prior
  obtain ⟨suffix,he⟩:=appends w (h.filterMap decodeHook)
  have eq : runPrefix g w (h.filterMap decodeHook) =
      ((runPrefix g w (h.filterMap decodeHook)).1,h.filterMap decodeHook++suffix) :=
    Prod.ext rfl he
  have hf:=frame w (h.filterMap decodeHook)
  rw [he,List.filterMap_append] at hf
  have empty : suffix.filterMap HookJournal.derivedReceipt=[] := by
    exact List.append_cancel_left (show (h.filterMap decodeHook).filterMap HookJournal.derivedReceipt ++
      suffix.filterMap HookJournal.derivedReceipt = (h.filterMap decodeHook).filterMap HookJournal.derivedReceipt ++ [] from by simpa using hf)
  have quiet : ∀r∈suffix,r.hook≠.sessionDerived := by
    intro r member kind
    have bad : ()∈suffix.filterMap HookJournal.derivedReceipt :=
      List.mem_filterMap.mpr ⟨r,member,by simp only [HookJournal.derivedReceipt,kind]⟩
    simp only [empty,List.not_mem_nil] at bad
  rw [focusPrefix_suffix Event.hook decodeHook g w h _ suffix eq]
  have next:=prior.append_hooks quiet
  refine ⟨suffix.map Event.hook,rfl,next,?_⟩
  cases (runPrefix g w (h.filterMap decodeHook)).1 <;> trivial

theorem focus_native_valid {α : Type} {g : WGPrefix HookJournal.Receipt α}
    (keeps : StatePrefixPreserves (fun h _ _=>HookJournal.ValidHistory h) HookJournal.ValidHistory g) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory
      (focusStatePrefix Event.hook decodeHook g) :=
  fun wg=>focus_valid (keeps wg)

theorem focus_native_paired {α : Type} {g : WGPrefix HookJournal.Receipt α}
    (appends : StateAppends g) (frame : StateHistoryFrame HookJournal.derivedReceipt g) :
    StatePrefixPreserves (fun h _ _=>Paired h) Paired
      (focusStatePrefix Event.hook decodeHook g) :=
  fun wg=>focus_paired (appends wg) (frame wg)

end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
