import SourceAdapter
import PairInsertWitness
namespace Binary.Pair.Insert.Witness
open Leanux Leanux.WG TrustBase Index
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem source_answer (linked : Bool) :
    ((Source.indexInsert (.keypair 0)).run (world linked)).toOption.map Prod.fst=some 7 := by
  cases linked <;> decide +kernel

theorem source_success (linked : Bool) :
    ∃ final, (Source.indexInsert (.keypair 0)).run (world linked)=.ok (7,final) := by
  have answer := source_answer linked
  cases result : (Source.indexInsert (.keypair 0)).run (world linked) with
  | error e => simp only [result,Except.toOption,Option.map_none] at answer; cases answer
  | ok pair =>
    rcases pair with ⟨value,final⟩
    have equal : value=7 := by simpa only [result,Except.toOption,Option.map_some,Option.some.injEq] using answer
    exact ⟨final,congrArg Except.ok (Prod.ext equal rfl)⟩
/-- The same two concrete states used by the executable witness runner.
The provider behavior and recorded-input interpretation remain explicit
contracts, just as in the general headline. -/
theorem executes (linked : Bool) (fetch : Int64 → Option Decoded)
    (decoder : IndexInsertDecoderAgreement fetch) (trace : TracePcContract fetch)
    (cmp : TraceCmp4Contract fetch) (bh : BhEnableContract fetch)
    (physical : RandomReturnContract fetch config) (inputAt : DataMem → List HiddenRecord → Prop)
    (coupling : RandomInputCoupling fetch config context.coverage (context.preempt+512)
      (codeEntry+0x79).toUInt64 inputAt)
    (input : inputAt (state linked).data.dmem [record 7]) :
    ∃ final, (Source.indexInsert (.keypair 0)).run (world linked)=.ok (7,final) ∧
      Eventually (instructionStep fetch)
        (Post names offsets context (state linked) (.ofNat stopAddr) config inputAt 7 final) (state linked) := by
  obtain ⟨final,accepted⟩ := source_success linked
  exact ⟨final,accepted,insert_checked fetch decoder trace cmp bh physical coupling
    (check linked) rfl input accepted⟩

#print axioms source_success
#print axioms executes
end Binary.Pair.Insert.Witness
