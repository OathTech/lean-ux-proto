import PairInsertRetryState
import PairInsertEnableSites
import PairInsertDisable

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

/-- Complete entry through the first retry boundary. Linked and unlinked
arguments share the same reconstructed, resident, unlinked owner afterward. -/
theorem retry_entry (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) (bh : BhEnableContract fetch) {n o c initial ra d owner base}
    (facts : FrameFacts n o c initial ra) (related : Corresponds n o initial.data.dmem d)
    (storage : storageCheck n o=true)
    (owners : Remove.ownership n o initial.data.dmem=.ok (Remove.targetOwnership d))
    (resident : Resident n o initial.data.dmem owner base)
    (argument : initial.data.regs.rsi.toNat=base) (entryPc : initial.pc=codeEntry) :
    Eventually (instructionStep fetch)
      (RetryPost n o c initial ra {d with indexTable := d.indexTable.filter (fun e => !(e.owner==owner))} owner base)
      initial := by
  have entry := unhash_entry fetch decoder trace facts related storage owners resident argument entryPc
  apply eventually_trans (instructionStep fetch) _ _ _ entry
  rintro unlinked ⟨pc,core,related,owned,resident,clear⟩
  have data : RetryData n o unlinked.data.dmem
      {d with indexTable := d.indexTable.filter (fun e => !(e.owner==owner))} owner base :=
    ⟨related,owned,resident,clear⟩
  have callback := core.callback fetch (codeEntry+0x4f) "L_ffffffff810f3100" trace
    (decoder _ _ (by rfl)) facts
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc callback)
  rintro called ⟨pc,core,_⟩
  have enable := enable_unhash fetch decoder bh facts core
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc enable)
  rintro enabled ⟨pc,core⟩
  have disable := disable_retry fetch decoder facts core
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (at_pc pc disable)
  rintro t ⟨pc,core⟩
  exact ⟨pc,core.rebase,data.frame core.frame⟩

#print axioms retry_entry
end Binary.Pair.Insert
