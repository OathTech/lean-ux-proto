import Leanux.Proofs.WG.Index.RetirementFirstPassFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.Framing
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

/-- The original entry first clears allowed IPs and then reads the saved list.
The landed account contract identifies that exact list, with no extra walk. -/
theorem retirement_entry_step
    (holders : DurableHolders) (cs : Ledger) (retired loans : Reservations)
    (w v : WGWorld) (a b : Ambient) (saved : List PeerId)
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs (retired ++ loans) w) (stable : StableRx cs w)
    (reserved : ∀ d, w.dev = some d → DeadHashedReserved retired d)
    (run : (BaseRemoval.entry.run w).run a = .ok ((saved,v),b)) :
    saved = holders.base.map Owner.slot ∧
    holders.Funded cs (retired ++ loans) v ∧ StableRx cs v ∧
    ConfiguredIdentity.Inv v ∧ BaseCoherence.Inv v ∧
    (∀ d, v.dev = some d → DeadHashedReserved retired d) := by
  obtain ⟨same,credit,stillStable⟩ := saved_entry_funded funded stable a b run
  have facts : Preserves
      (fun g : WGWorld => ConfiguredIdentity.Inv g ∧ BaseCoherence.Inv g ∧
        ∀ d, g.dev = some d → DeadHashedReserved retired d) BaseRemoval.entry := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro before time returned after final hi execution
    unfold BaseRemoval.entry at execution
    rw [MaterialOrigin.bind_ok_ambient] at execution
    obtain ⟨u,cleared,c,clear,tail⟩ := execution
    rw [MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨d,read,e,getter,finish⟩ := tail
    obtain ⟨stateEq,timeEq,device⟩ := DecryptCarrier.getDev_current c e getter
    subst read
    subst e
    have last : (d.peerList = returned ∧ cleared = after) ∧ c = final := by
      simpa using finish
    obtain ⟨⟨_,sameState⟩,_⟩ := last
    rw [← sameState]
    exact ⟨(hoare_iff_run_ambient _ _ _).mp
        (ConfiguredRemoval.frame ConfiguredIdentity.allowedipsFree_view)
        before time u cleared c hi.1 clear,
      BaseCoherence.transport hi.2.1
        ((ProjectedAction.iff_run_ambient _ _ _).mp BaseCoherence.free_view
          before time u cleared c clear),
      (hoare_iff_run_ambient _ _ _).mp (free_deadHashedReserved retired)
        before time u cleared c hi.2.2 clear⟩
  exact ⟨same,credit,stillStable,
    (hoare_iff_run_ambient _ _ _).mp facts w a saved v b
      ⟨configured,base,reserved⟩ run⟩


/-- The actual first mark loop, before its terminal-false branch. -/
def retirementMarkPass (saved : List PeerId) : WG.M Unit := do
  for pid in saved do
    _ ← branch .peerRemoveAllIter1 true
    peerMakeDead pid

/-- Original trie free, saved-list read and mark pass. No cleanup or payment
has run at this source cut. -/
def retirementFirstPass : WG.M (List PeerId) := do
  let saved ← BaseRemoval.entry
  retirementMarkPass saved
  pure saved

/-- The untouched remainder: terminal first-pass branch, saved cleanup pass,
and its terminal branch. Its original callback failures are preserved. -/
def retirementAfterFirstPass (saved : List PeerId) : WG.M Unit := do
  _ ← branch .peerRemoveAllIter1 false
  for pid in saved do
    _ ← branch .peerRemoveAllIter2 true
    peerRemoveAfterDead pid
  _ ← branch .peerRemoveAllIter2 false
  pure ()

/-- Exact source equality on every outcome, not only normal returns. -/
theorem peerRemoveAll_retirement_factor :
    peerRemoveAll = (do
      let saved ← retirementFirstPass
      retirementAfterFirstPass saved) := by
  rw [BaseRemoval.peerRemoveAll_entry]
  simp only [retirementFirstPass,retirementMarkPass,retirementAfterFirstPass,
    bind_assoc,pure_bind]

/-- The saved first pass is derived from original entry funding and
reservation facts. The budget transfers exactly the original base occurrences
ahead of the prior retirement prefix, before cleanup spends any occurrence. -/
theorem retirementFirstPass_step
    (holders : DurableHolders) (cs : Ledger) (retired loans : Reservations)
    (w v : WGWorld) (a b : Ambient) (saved : List PeerId)
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs (retired ++ loans) w) (stable : StableRx cs w)
    (reserved : ∀ d, w.dev = some d → DeadHashedReserved retired d)
    (run : (retirementFirstPass.run w).run a = .ok ((saved,v),b)) :
    saved = holders.base.map Owner.slot ∧
    (holders.withoutBase []).Funded cs ((holders.base ++ retired) ++ loans) v ∧
    StableRx cs v ∧
    (∀ final, v.dev = some final → DeadHashedReserved (holders.base ++ retired) final) := by
  unfold retirementFirstPass at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨dead,entered,c,entry,rest⟩ := run
  obtain ⟨same,credit,stillStable,configuredEntry,baseEntry,reservedEntry⟩ :=
    retirement_entry_step holders cs retired loans w entered a c dead
      configured base funded stable reserved entry
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨u,marked,e,mark,finish⟩ := rest
  cases u
  have last : (dead = saved ∧ marked = v) ∧ e = b := by simpa using finish
  obtain ⟨⟨savedEq,stateEq⟩,timeEq⟩ := last
  subst saved
  subst v
  subst b
  refine ⟨same,?_⟩
  apply saved_makeDead_retirement_step holders cs retired loans entered marked c e
    configuredEntry baseEntry credit stillStable reservedEntry
  simpa only [retirementMarkPass,same] using mark

/-- Every normal original bulk removal has this same-run first-pass cut.
Only the cut receives the retirement budget: the actual remaining cleanup
execution is retained explicitly, without asserting its endpoint obligation. -/
theorem peerRemoveAll_retirement_cut
    (holders : DurableHolders) (cs : Ledger) (retired loans : Reservations)
    (w v : WGWorld) (a b : Ambient)
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs (retired ++ loans) w) (stable : StableRx cs w)
    (reserved : ∀ d, w.dev = some d → DeadHashedReserved retired d)
    (run : (peerRemoveAll.run w).run a = .ok (((),v),b)) :
    ∃ saved marked c,
      (retirementFirstPass.run w).run a = .ok ((saved,marked),c) ∧
      ((retirementAfterFirstPass saved).run marked).run c = .ok (((),v),b) ∧
      saved = holders.base.map Owner.slot ∧
      (holders.withoutBase []).Funded cs ((holders.base ++ retired) ++ loans) marked ∧
      StableRx cs marked ∧
      (∀ final, marked.dev = some final →
        DeadHashedReserved (holders.base ++ retired) final) := by
  rw [peerRemoveAll_retirement_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨saved,marked,c,firstRun,suffix⟩ := run
  exact ⟨saved,marked,c,firstRun,suffix,
    retirementFirstPass_step holders cs retired loans w marked a c saved
      configured base funded stable reserved firstRun⟩

end Leanux.Proofs.WG.Index
