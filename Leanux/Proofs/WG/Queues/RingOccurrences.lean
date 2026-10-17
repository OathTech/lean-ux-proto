import Leanux.Proofs.WG.Queues.RingJournal

/-! Each offer gets a fresh ordinal, including refused offers. Ordinals are
journal occurrences, not payload identities or allocation lifetimes. -/
namespace Leanux.Proofs.WG.Queues.Ring.Journal
open Leanux Leanux.WG

def inputs (cs : List (Command α)) : List α := cs.filterMap fun c => match c with
  | .offer x => some x
  | .poll => none

def tagCommands (next : Nat) : List (Command α) → List (Command (Nat × α))
  | [] => []
  | .offer x :: cs => .offer (next, x) :: tagCommands (next + 1) cs
  | .poll :: cs => .poll :: tagCommands next cs

theorem tagCommands_erase (next : Nat) (cs : List (Command α)) :
    (tagCommands next cs).map (Command.map Prod.snd) = cs := by
  induction cs generalizing next with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [tagCommands, Command.map, ih]

theorem tagCommands_ordinals (next : Nat) (cs : List (Command α)) :
    (inputs (tagCommands next cs)).map Prod.fst = List.range' next (inputs cs).length := by
  induction cs generalizing next with
  | nil => simp [inputs, tagCommands]
  | cons c cs ih =>
    cases c with
    | offer x => simpa [inputs, tagCommands, List.range'_succ] using ih (next + 1)
    | poll => simpa [inputs, tagCommands] using ih next

theorem run_offered (r : PtrRing α) (cs : List (Command α)) :
    offered (run r cs).1 = inputs cs := by
  induction cs generalizing r with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | offer x => simpa [run, step, offered, inputs] using ih (tryProduce r x).2
    | poll => simpa [run, step, offered, inputs] using ih r.consume.2

theorem admitted_sublist_offered (h : List (Event α)) :
    (admitted h).Sublist (offered h) := by
  induction h with
  | nil => exact .refl []
  | cons e h ih =>
    cases e with
    | offered x ok =>
      cases ok
      · simpa [admitted, offered] using ih.cons x
      · simpa [admitted, offered] using ih.cons_cons x
    | polled x => simpa [admitted, offered] using ih

/-- Forgetting ordinals preserves every offer outcome, every poll result and
the complete final physical ring, for arbitrary starting rings. -/
theorem tagged_erasure (r : PtrRing (Nat × α)) (next : Nat) (cs : List (Command α)) :
    run (mapRing Prod.snd r) cs =
      ((run r (tagCommands next cs)).1.map (Event.map Prod.snd),
        mapRing Prod.snd (run r (tagCommands next cs)).2) := by
  simpa only [tagCommands_erase] using run_map Prod.snd r (tagCommands next cs)

theorem tagged_initialized_erasure (n next : Nat) (cs : List (Command α)) :
    run (PtrRing.init n) cs =
      ((run (PtrRing.init n) (tagCommands next cs)).1.map (Event.map Prod.snd),
        mapRing Prod.snd (run (PtrRing.init n) (tagCommands next cs)).2) := by
  simpa only [init_map] using tagged_erasure (PtrRing.init n) next cs

theorem tagged_offers (r : PtrRing (Nat × α)) (next : Nat) (cs : List (Command α)) :
    (offered (run r (tagCommands next cs)).1).map Prod.fst =
      List.range' next (inputs cs).length := by
  rw [run_offered, tagCommands_ordinals]

theorem tagged_admitted_nodup (r : PtrRing (Nat × α)) (next : Nat) (cs : List (Command α)) :
    ((admitted (run r (tagCommands next cs)).1).map Prod.fst).Nodup := by
  apply List.Nodup.sublist ((admitted_sublist_offered _).map Prod.fst)
  rw [tagged_offers]
  exact List.nodup_range'

/-- Consumed and pending live occurrences partition admissions. Their joint
ordinal list has no duplicates; repeated payloads are permitted. Zero size is
included. No assertion of eventual consumption is made. -/
theorem tagged_conservation (n next : Nat) (cs : List (Command α)) :
    let out := run (PtrRing.init n) (tagCommands next cs)
    admitted out.1 = consumed out.1 ++ out.2.items ∧
      ((consumed out.1 ++ out.2.items).map Prod.fst).Nodup := by
  dsimp only
  have hc := conservation_all n (tagCommands next cs)
  exact ⟨hc, hc ▸ tagged_admitted_nodup (PtrRing.init n) next cs⟩

end Leanux.Proofs.WG.Queues.Ring.Journal
