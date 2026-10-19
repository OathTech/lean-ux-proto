import LookupHelperCall
import LookupFirstHelperEntry
namespace Binary.LookupRelation.First
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation PeerCountPhase Callback LookupHistory.First
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}
/-- The lookup's actual owner load and helper CALL, including both cuts,
    preserve the source World and append its exact call marker. -/
theorem peer_call_simulation (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (c : Config) (world : World)
    (s : MachineData) (safe : s.regs.rsp≠outer+8) (peer : Address) (history : List MachineState) (seen : List Point)
    (source : List MirrorHistory.Point)
    (field : s.dmem.loadInt s.regs.rbx.toBitVec 8 = some (peer.toNat : Int))
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true)
    (related : R c history seen ⟨s, Image.Lookup.entry+0xb2⟩ world)
    (observed : observe c.rxSection history = .ok seen)
    (matched : MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen source)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection history source)
    (latest : source.getLast?.map (·.world) = some world)
    (initial : scan none history = none) (noReturn : lastHelperReturn seen = none)
    (apart : ∀ v, project c world = some v → ∀ a, Reads c v a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t =>
      t.machine = peerCalled s peer ∧
      t.history = history ++ [⟨peerArgument s peer, Image.Lookup.entry+0xb5⟩, t.machine] ∧
      StableExtension history t.history ∧
      observe c.rxSection t.history = .ok (seen ++ [call "wg_peer_get_maybe_zero" t.machine]) ∧
      MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection t.history)
        (seen ++ [call "wg_peer_get_maybe_zero" t.machine]) (source ++ [⟨.call "wg_peer_get_maybe_zero", world⟩]) ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection t.history
        (source ++ [⟨.call "wg_peer_get_maybe_zero", world⟩]) ∧
      R c t.history (seen ++ [call "wg_peer_get_maybe_zero" t.machine]) t.machine world)
      ⟨⟨s, Image.Lookup.entry+0xb2⟩, history⟩ := by
  let moved : MachineState := ⟨peerArgument s peer, Image.Lookup.entry+0xb5⟩
  let called := peerCalled s peer
  have stable := peer_call_stable s peer history related.1
  have firstStable : StableExtension history (history ++ [moved]) := by
    have result := StableExtension.of_ordinary history.dropLast ⟨s, Image.Lookup.entry+0xb2⟩ [moved] (by
      intro q member
      simp only [List.dropLast_cons_cons, List.dropLast_singleton, List.mem_singleton] at member
      subst q
      constructor <;> simp [Image.Lookup.entry, Image.PeerGet.entry])
    have grouped : StableExtension (history.dropLast ++ [⟨s, Image.Lookup.entry+0xb2⟩])
        ((history.dropLast ++ [⟨s, Image.Lookup.entry+0xb2⟩]) ++ [moved]) := by
      simpa only [List.append_assoc, List.singleton_append] using result
    simpa only [history_restore related.1] using grouped
  have firstObs : observe c.rxSection (history ++ [moved]) = .ok seen := by
    have h := observe_snoc c.rxSection history ⟨s, Image.Lookup.entry+0xb2⟩ moved seen [] related.1 observed (by
      simp [LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
    simpa only [List.append_nil] using h
  have allObs : observe c.rxSection ((history ++ [moved]) ++ [called]) =
      .ok (seen ++ [call "wg_peer_get_maybe_zero" called]) :=
    observe_snoc c.rxSection (history ++ [moved]) moved called seen _ (by simp) firstObs (by
      simp [moved, called, peerCalled, Instrumentation.calledState, LookupObservation.edge,
        Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  have firstR := related.frame_no_pending c world history (history ++ [moved]) seen seen
    ⟨s, Image.Lookup.entry+0xb2⟩ moved (by simp) initial (by rw [firstStable.final, initial]) noReturn noReturn rfl
    (fun _ => False) (by intro a _; rfl) (by intro v projected a read; simp)
  have endR := related.frame_no_pending c world history ((history ++ [moved]) ++ [called]) seen
    (seen ++ [call "wg_peer_get_maybe_zero" called]) ⟨s, Image.Lookup.entry+0xb2⟩ called (by simp) initial
    (by simpa only [List.append_assoc, List.singleton_append] using (stable.final none).trans initial)
    noReturn (by simp [lastHelperReturn, call]) (by simp [call]) _ (peer_call_frame s peer) apart
  have firstMatched := ExecutedCorrespondence.matched_append_history matched [moved]
  have point := helper_call_point c (history ++ [moved]) seen called world firstObs allObs endR
  have allMatched := (ExecutedCorrespondence.matched_append_history firstMatched [called]).append
    (by simpa only [List.nil_append] using point)
  have firstCuts := aligned.snoc moved (by
    intro _
    cases last : source.getLast? with
    | none => rw [last] at latest; cases latest
    | some point =>
      have worldEq : point.world = world := by rw [last] at latest; exact Option.some.inj latest
      refine ⟨seen, point, firstObs, ?_, ?_, ?_⟩
      · refine ⟨by rw [matched.length_eq]; exact Nat.le_refl _, ?_⟩
        simpa only [matched.length_eq, List.take_length] using firstMatched
      · simpa only [matched.length_eq, List.take_length] using last
      · simpa only [worldEq] using firstR)
  have allCuts := (firstCuts.append_source [⟨.call "wg_peer_get_maybe_zero", world⟩]).snoc called (by
    intro _
    have sizes := allMatched.length_eq
    refine ⟨_, ⟨.call "wg_peer_get_maybe_zero", world⟩, allObs, ?_, ?_, endR⟩
    · refine ⟨by omega, ?_⟩
      rw [sizes, List.take_length]
      exact allMatched
    · rw [sizes, List.take_length]
      simp)
  have guarded := history_guard_suffix (guard := StackGuard outer)
      (historySteps_eventually fetch 2 _ _ (peer_call_history fetch agree s peer field mapped history)) related.1 (by
    rintro t ⟨machine, recorded⟩
    refine ⟨_,recorded,?_⟩
    intro q member
    simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals change s.regs.rsp≠outer+8
    all_goals exact safe)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ guarded
  rintro t ⟨machine, recorded⟩
  refine ⟨machine, recorded, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [recorded, machine] using stable
  · simpa only [recorded, machine, List.append_assoc, List.singleton_append, moved, called] using allObs
  · simpa only [recorded, machine, List.append_assoc, List.singleton_append, moved, called] using allMatched
  · simpa only [recorded, machine, List.append_assoc, List.singleton_append, moved, called] using allCuts
  · simpa only [recorded, machine, List.append_assoc, List.singleton_append, moved, called] using endR

#print axioms peer_call_stable
#print axioms helper_call_point
#print axioms peer_call_simulation
end Binary.LookupRelation.First
