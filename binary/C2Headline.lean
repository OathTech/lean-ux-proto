import C2Callbacks
import C2Range
import C2Sequences

/-! Result C2, the closed theorems that need only the mirror.

The three clauses of `HeadlineRefinement` that do not mention the proof tree, with no
hypothesis left: the assembly theorems of `C2CutAssembly` applied to the work packages'
theorems. The fourth clause (`NoCounterAcceptedTwice`) and the headline itself are in the
bridge library (`bridge/C2Bridge.lean`), which imports the proof tree's `CounterWindow`.

Nothing is proved here but the joins. The first section restates each interface
proposition beside the theorem that closes it, so that the build fails if a package's
theorem stops having the stated type. -/
namespace Binary.C2
open Binary TrustBase Leanux
local instance : Labels := Binary.Image.linkedLabels

/-! ## The packages' theorems at their interface types -/

-- Work package 1: the three callback rules, the adapter, `bts`, the layout, the call sites.
example : Callback.Cmp8.PcRule := Callback.Cmp8.pc_rule
example : Callback.Cmp8.Cmp8Rule := Callback.Cmp8.cmp8_rule
example : Callback.Cmp8.ConstCmp8Rule := Callback.Cmp8.const_cmp8_rule
example : StubsAgree := stubs_agree
example : BtsSupported := bts_supported
example : RegionsLaidOut := regions_laid_out
example : PcSite := pc_site
example : Cmp8Site := cmp8_site
example : ConstCmp8Site := const_cmp8_site

-- Work package 2: the five segments, from package 1's propositions.
example : RegionsLaidOut → PcSite → Cmp8Site → ConstCmp8Site → HeadSegment := head_segment
example : RegionsLaidOut → PcSite → Cmp8Site → AdvanceEnters := advance_enters
example : RegionsLaidOut → PcSite → Cmp8Site → LoopIteration := loop_iteration
example : RegionsLaidOut → PcSite → AdvanceStores := advance_stores
example : RegionsLaidOut → PcSite → TailSegment := tail_segment

-- Work package 3: representation, the mirror link, sequences, the witness.
example : WindowMapped := window_mapped
example : WindowOfFields := window_of_fields
example : FieldsOfWindow := fields_of_window
example : FieldsFit := fields_fit
example : FieldsRetained := fields_retained
example : FieldsMapped := fields_mapped
example : MirrorFollowsSpec := mirror_follows_spec
example : WorldHolds := world_holds
example : FirstExitDetermined := first_exit_determined
example : FirstExitExists := first_exit_exists
example : WitnessStart := witness_start
example : Representation := representation

/-! ## The joins -/

/-- The five segments of the range, closed: work package 2's theorems on work package
1's. -/
theorem execution_closed : Execution :=
  execution regions_laid_out pc_site cmp8_site const_cmp8_site

/-- The range against the pivot, closed. -/
theorem range_simulates_closed : RangeSimulates :=
  range_simulates execution_closed

/-- CLAUSE 1 of the headline, closed. -/
theorem exits_cleanly : ExitsCleanly :=
  exits_cleanly_of_parts range_simulates_closed representation.mapped

/-- THE REFINEMENT, closed: the range computes the mirror's `counterValidate`. -/
theorem refines : Refines :=
  refines_of_parts range_simulates_closed representation

/-- THE WITNESS, closed: a replayed packet counter, accepted and then refused. -/
theorem replay_witness : ReplayWitness :=
  replay_witness_of_parts (strong_refines range_simulates_closed representation)
    representation witness_start

#print axioms exits_cleanly
#print axioms refines
#print axioms replay_witness
end Binary.C2
