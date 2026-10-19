import CallbackContracts
import PairLookupAdequacy
import PairRemoveAdequacy
import PairReplaceAdequacy
import PairInsertAdequacy
import PairSequenceAdequacy
import PairInsertSequenceAdequacy

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG TrustBase
local instance : Labels := Image.linkedLabels

/-- The five shared callbacks are executed from their image proofs;
only decoding, the original entry domain and any explicitly listed environment
or random-service premises remain. -/
theorem lookup_from_image (fetch : Int64 → Option Decoded)
    (decoder : AnchoredDecoderAgreement fetch) (services : ServiceDecoderAgreement fetch)
     
    {n o coverage initial w query kinds ra answer finalWorld}
    (checked : Pre n o coverage initial w query kinds ra)
    (accepted : (WG.indexLookup kinds query).run w=.ok (answer,finalWorld)) :
    Eventually (instructionStep fetch) (Post n o coverage initial ra answer finalWorld) initial := by
  exact lookup_checked fetch decoder
    (Callback.pc_contract fetch services) (Callback.cmp4_contract fetch services) (Callback.const_cmp4_contract fetch services) (Callback.const_cmp1_contract fetch services) (Callback.bh_contract fetch services)
    checked accepted

#print axioms lookup_from_image
end Binary.Pair.IndexLookup

namespace Binary.Pair.Remove
open Leanux Leanux.WG TrustBase
local instance : Labels := Image.linkedLabels

/-- The five shared callbacks are executed from their image proofs;
only decoding, the original entry domain and any explicitly listed environment
or random-service premises remain. -/
theorem remove_from_image (fetch : Int64 → Option Decoded) (decoder : IndexRemoveDecoderAgreement fetch)
    (services : ServiceDecoderAgreement fetch) 
    {n o c initial w owner ra final} (checked : Pre n o c initial w owner ra)
    (accepted : (WG.indexRemove owner).run w=.ok ((),final)) :
    Eventually (instructionStep fetch) (Post n o c initial ra final) initial := by
  exact remove_checked fetch decoder
    (Callback.pc_contract fetch services) (Callback.bh_contract fetch services)
    checked accepted

#print axioms remove_from_image
end Binary.Pair.Remove

namespace Binary.Pair.Replace
open Leanux Leanux.WG TrustBase
local instance : Labels := Image.linkedLabels

/-- The five shared callbacks are executed from their image proofs;
only decoding, the original entry domain and any explicitly listed environment
or random-service premises remain. -/
theorem replace_from_image (fetch : Int64 → Option Decoded) (decoder : IndexReplaceDecoderAgreement fetch)
    (services : ServiceDecoderAgreement fetch) 
    {n o c initial w pid kid ra answer final} (checked : Pre n o c initial w pid kid ra)
    (accepted : (WG.indexReplaceHandshake pid kid).run w=.ok (answer,final)) :
    Eventually (instructionStep fetch) (Post n o c initial ra answer final) initial := by
  exact replace_checked fetch decoder
    (Callback.pc_contract fetch services) (Callback.bh_contract fetch services)
    checked accepted

#print axioms replace_from_image
end Binary.Pair.Replace

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase
local instance : Labels := Image.linkedLabels

/-- The five shared callbacks are executed from their image proofs;
only decoding, the original entry domain and any explicitly listed environment
or random-service premises remain. -/
theorem insert_from_image (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (services : ServiceDecoderAgreement fetch)  
    {n o c initial ra config inputAt w owner records answer final}
    (physical : RandomReturnContract fetch config)
    (coupling : RandomInputCoupling fetch config c.coverage (c.preempt+512) (codeEntry+0x79).toUInt64 inputAt)
    (pre : Pre n o c initial w owner ra config)
    (supplied : w.hidden=some records) (input : inputAt initial.data.dmem records)
    (accepted : (WG.indexInsert owner).run w=.ok (answer,final)) :
    Eventually (instructionStep fetch) (Post n o c initial ra config inputAt answer final) initial := by
  exact insert_checked fetch decoder
    (Callback.pc_contract fetch services) (Callback.cmp4_contract fetch services) (Callback.bh_contract fetch services)
    physical coupling pre supplied input accepted

#print axioms insert_from_image
end Binary.Pair.Insert

namespace Binary.Pair.Sequence
open Leanux Leanux.WG TrustBase
local instance : Labels := Image.linkedLabels

/-- The five shared callbacks are executed from their image proofs;
only decoding, the original entry domain and any explicitly listed environment
or random-service premises remain. -/
theorem sequence_from_image (fetch : Int64 → Option Decoded)
    (lookupDecoder : AnchoredDecoderAgreement fetch)
    (removeDecoder : IndexRemoveDecoderAgreement fetch)
    (replaceDecoder : IndexReplaceDecoderAgreement fetch)
    (services : ServiceDecoderAgreement fetch) 
     (permissions : Permissions) (onlineCPUs : Nat) (externalActions : List Nat)
    {n o c initial w ra calls answers finalWorld}
    (environment : SerializedEnvironment onlineCPUs externalActions)
    (access : ReturningDomainPermissions fetch permissions ra (EntryDomain n initial ra))
    (checked : initialCheck n o c initial w ra=.ok ())
    (admissible : AdmissibleSequence n calls w)
    (accepted : (program calls).run w=.ok (answers,finalWorld)) :
    Execute fetch n initial ra calls initial
      (SequencePost fetch permissions onlineCPUs externalActions n o c initial initial ra answers finalWorld) := by
  exact sequence_checked fetch lookupDecoder removeDecoder replaceDecoder
    (Callback.pc_contract fetch services) (Callback.cmp4_contract fetch services) (Callback.const_cmp4_contract fetch services) (Callback.const_cmp1_contract fetch services) (Callback.bh_contract fetch services)
    permissions onlineCPUs externalActions environment access checked admissible accepted

#print axioms sequence_from_image
end Binary.Pair.Sequence

namespace Binary.Pair.InsertSequence
open Leanux Leanux.WG TrustBase
local instance : Labels := Image.linkedLabels

/-- The five shared callbacks are executed from their image proofs;
only decoding, the original entry domain and any explicitly listed environment
or random-service premises remain. -/
theorem sequence_from_image (fetch : Int64 → Option Decoded)
    (lookupDecoder : AnchoredDecoderAgreement fetch)
    (removeDecoder : IndexRemoveDecoderAgreement fetch)
    (replaceDecoder : IndexReplaceDecoderAgreement fetch)
    (insertDecoder : IndexInsertDecoderAgreement fetch)
    (services : ServiceDecoderAgreement fetch) 
     (permissions : Permissions) (onlineCPUs : Nat) (externalActions : List Nat)
    {n o c initial w ra calls answers finalWorld config inputAt records}
    (environment : SerializedEnvironment onlineCPUs externalActions)
    (access : ReturningDomainPermissions fetch permissions ra (EntryDomain n o c initial ra config inputAt))
    (physical : RandomReturnContract fetch config)
    (coupling : RandomInputCoupling fetch config c.coverage (c.preempt+512)
      (Insert.codeEntry+0x79).toUInt64 inputAt)
    (checked : initialCheck n o c initial w ra config=.ok ())
    (supplied : w.hidden=some records) (input : inputAt initial.data.dmem records)
    (admissible : AdmissibleSequence n calls w)
    (accepted : (program calls).run w=.ok (answers,finalWorld)) :
    Execute fetch n initial ra calls initial
      (SequencePost fetch permissions onlineCPUs externalActions n o c initial initial ra config inputAt calls w answers finalWorld) := by
  exact sequence_checked fetch lookupDecoder removeDecoder replaceDecoder insertDecoder
    (Callback.pc_contract fetch services) (Callback.cmp4_contract fetch services) (Callback.const_cmp4_contract fetch services) (Callback.const_cmp1_contract fetch services) (Callback.bh_contract fetch services)
    permissions onlineCPUs externalActions environment access physical coupling checked supplied input admissible accepted

#print axioms sequence_from_image
end Binary.Pair.InsertSequence

