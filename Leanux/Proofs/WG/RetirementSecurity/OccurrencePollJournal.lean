import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDriverCuts
import Leanux.Proofs.WG.TransmitSecurity.JournalProjection

/-! Physical ownership certificates attached to the shared journal's actual
poll receipts. The observer is unchanged; every certificate names its real
input world and the native poll execution represented by that receipt. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open OccurrenceStack TransmitSecurity

def polled? : Journal.Event → Option (RunWitness (Option (List SkbId)))
  | .polled r => some r
  | _ => none

def Certificate (r : RunWitness (Option (List SkbId))) : Prop :=
  Ready [] [] r.before.wg ∧ r.Valid (liftWG TxRing.pollSource) ∧
    Ready [] r.value.toList r.after.wg

def Safe (h : List Journal.Event) : Prop :=
  ∀ r ∈ h.filterMap polled?, Certificate r

def Inv (active : List (List SkbId)) (h : List Journal.Event) (w : World) : Prop :=
  Ready [] active w.wg ∧ Safe h

theorem Safe.frame (before : Safe h) (same : j.filterMap polled? = h.filterMap polled?) : Safe j := by
  simpa only [Safe,same] using before

theorem Safe.append (before : Safe h) (receipt : Certificate r) : Safe (h ++ [.polled r]) := by
  intro q member
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,polled?,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with old | same
  · exact before q old
  · subst q
    exact receipt

theorem poll : PrefixEnsures (Inv []) Safe Journal.poll
    (fun item h w => Inv item.toList h w) := by
  intro w h before
  let action := focusPrefix Journal.Event.ring Journal.ring? TxRing.poll
  have append : Appends action := Appends.focus _ _ _
  have quiet : HistoryFrame polled? action := focusPrefix_other _ _ _ (fun _ => rfl) _
  have erase : ErasesPrefix action (liftWG TxRing.pollSource) :=
    focusPrefix_erases _ _ TxRing.poll_erases
  obtain ⟨suffix,extension⟩ := append w h
  have oldSafe : Safe (runPrefix action w h).2 := before.2.frame (quiet w h)
  unfold Journal.poll
  rw [runPrefix_receiptObserved]
  rw [show focusPrefix Journal.Event.ring Journal.ring? TxRing.poll = action from rfl]
  cases actual : runPrefix action w h with
  | mk outcome j =>
    rw [actual] at extension oldSafe
    cases outcome with
    | error stop => exact ⟨suffix,extension,oldSafe,True.intro⟩
    | ok result =>
      obtain ⟨item,v⟩ := result
      have native : (liftWG TxRing.pollSource).run w = .ok (item,v) := by
        have erases := erase w h
        rw [actual] at erases
        exact erases.symm
      have output : Ready [] item.toList v.wg := by
        have observed : (runPrefix Journal.poll w h).1 = .ok (item,v) := by
          change (runPrefix (receiptObserved action Journal.Event.polled) w h).1 = _
          rw [runPrefix_receiptObserved,actual]
        simpa only [List.append_nil] using
          OccurrenceDriverCuts.poll Journal.hooks_projects before.1 h observed
      have safe := oldSafe.append (r := ⟨item,w,v⟩) ⟨before.1,native,output⟩
      refine ⟨suffix ++ [.polled ⟨item,w,v⟩],?_,safe,output,safe⟩
      simpa only [List.append_assoc] using
        congrArg (fun j => j ++ [.polled ⟨item,w,v⟩]) extension

end Leanux.Proofs.WG.RetirementSecurity.OccurrencePollJournal
