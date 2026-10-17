import Leanux.Proofs.WG.Queues.TrafficOccurrences

/-! Positions in existing source paths, independently of packet acceptance.
These cursors do not run a second caller or recompute a ledger. The source
path already supplies every exact Step; a cursor exposes one such occurrence.
Acceptance at that cut then selects the existing admission query, even when
the admitted carrier is removed before the enclosing path returns. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.AdmissionSourceCuts
open Leanux Leanux.WG Leanux.Proofs.Logged
open TrafficOccurrences

/-- A specified source Step in an already established flood path. No packet,
acceptance, final membership, or fate appears in this cursor. -/
inductive FloodCut (family : Nat) (src : SkbSource)
    {msg : List UInt8} {before after : Ledger} {a b : World}
    {j l : List RxHistory.Event}
    (step : FloodLoop.Step family src msg before after a b j l) :
    {messages : List (List UInt8)} → {cs : Ledger} → {w : World} → {h : List RxHistory.Event} →
    {next : Ledger} → {v : World} → {k : List RxHistory.Event} →
    FloodLoop.Path family src messages cs w h next v k → Nat → Prop
  | here (tail : FloodLoop.Path family src messages after b l next v k) :
      FloodCut family src step (.cons step tail) 0
  | later (front : FloodLoop.Step family src first cs middle w u h i)
      (tail : FloodLoop.Path family src messages middle u i next v k)
      (cut : FloodCut family src step tail index) :
      FloodCut family src step (.cons front tail) (index+1)

theorem flood_selected
    {step : FloodLoop.Step family src msg before after a b j l}
    {path : FloodLoop.Path family src messages cs w h next v k}
    (cut : FloodCut family src step path index)
    (accepted : FloodStepAdmission family src msg before after a b j l c) :
    FloodChosen family src c path index := by
  induction cut with
  | here tail => exact .here step tail accepted
  | later front tail cut ih => exact .later front tail ih

theorem flood_at
    {step : FloodLoop.Step family src msg before after a b j l}
    {path : FloodLoop.Path family src messages cs w h next v k}
    (cut : FloodCut family src step path index) : messages[index]? = some msg := by
  induction cut with
  | here tail => rfl
  | later front tail cut ih => exact ih

/-- Every list position of a normal flood path has its actual source cut.
The index remains a position when two messages have equal values. -/
theorem flood_total (path : FloodLoop.Path family src messages cs w h next v k)
    (bound : index < messages.length) :
    ∃ msg before after a b j l,
      ∃ step : FloodLoop.Step family src msg before after a b j l,
        FloodCut family src step path index := by
  induction path generalizing index with
  | nil => simp at bound
  | cons step tail ih =>
    cases index with
    | zero => exact ⟨_,_,_,_,_,_,_,step,.here tail⟩
    | succ index =>
      obtain ⟨msg,before,after,a,b,j,l,chosen,cut⟩ := ih (Nat.lt_of_succ_lt_succ bound)
      exact ⟨msg,before,after,a,b,j,l,chosen,.later step tail cut⟩

theorem flood_cut_fate
    {step : FloodLoop.Step family src msg before after a b j l}
    {path : FloodLoop.Path family src messages cs w h next v k}
    (cut : FloodCut family src step path index)
    (accepted : FloodStepAdmission family src msg before after a b j l c) :
    Fate c next h k :=
  floodChosen_fate (flood_selected cut accepted)

/-- A source cursor follows only actual done/yield constructors. In
particular there is no later cut after a `.done` body. -/
inductive BatchCut (d : Device)
    {cqes : List Int} {item : Env.BatchItem} {result : ForInStep (List Int)}
    {before after : Ledger} {a b : World} {j l : List RxHistory.Event}
    (step : BatchAccount.Step d cqes item result before after a b j l) :
    {entries : List Env.BatchItem} → {initial : List Int} →
    {cs : Ledger} → {w : World} → {h : List RxHistory.Event} → {out : List Int} →
    {next : Ledger} → {v : World} → {k : List RxHistory.Event} →
    BatchAccount.Path d entries initial cs w h out next v k → Nat → Prop
  | done (same : result = .done out) :
      BatchCut d step (.done (same ▸ step)) 0
  | here (same : result = .yield qs)
      (tail : BatchAccount.Path d entries qs after b l out next v k) :
      BatchCut d step (.yield (same ▸ step) tail) 0
  | later (front : BatchAccount.Step d initial first (.yield qs) cs middle w u h i)
      (tail : BatchAccount.Path d entries qs middle u i out next v k)
      (cut : BatchCut d step tail index) :
      BatchCut d step (.yield front tail) (index+1)

theorem batch_selected
    {step : BatchAccount.Step d cqes item result before after a b j l}
    {path : BatchAccount.Path d entries initial cs w h out next v k}
    (cut : BatchCut d step path index)
    (accepted : BatchStepAdmission d cqes item result before after a b j l c) :
    BatchChosen d c path index := by
  induction cut with
  | done same => cases same; exact .done step accepted
  | here same tail => cases same; exact .here step tail accepted
  | later front tail cut ih => exact .later front tail ih

theorem batch_at
    {step : BatchAccount.Step d cqes item result before after a b j l}
    {path : BatchAccount.Path d entries initial cs w h out next v k}
    (cut : BatchCut d step path index) : entries[index]? = some item := by
  induction cut with
  | done same => rfl
  | here same tail => rfl
  | later front tail cut ih => exact ih

theorem batch_first (path : BatchAccount.Path d (item::entries) initial cs w h out next v k) :
    ∃ result middle u j,
      ∃ step : BatchAccount.Step d initial item result cs middle w u h j,
        BatchCut d step path 0 := by
  cases path with
  | done step => exact ⟨_,_,_,_,step,.done rfl⟩
  | yield step tail => exact ⟨_,_,_,_,step,.here rfl tail⟩

theorem batch_cut_fate
    {step : BatchAccount.Step d cqes item result before after a b j l}
    {path : BatchAccount.Path d entries initial cs w h out next v k}
    (cut : BatchCut d step path index)
    (accepted : BatchStepAdmission d cqes item result before after a b j l c) :
    Fate c next h k :=
  batchChosen_fate (batch_selected cut accepted)

end Leanux.Proofs.WG.Queues.RxCredits.AdmissionSourceCuts
