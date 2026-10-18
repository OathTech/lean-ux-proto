import PairRemoveEnvironment
import PairReplaceEnvironment
import PairLookupEnvironment
import PairRemoveWitness
import PairReplaceWitness
import PairSequenceAdequacy

/-! One replay/export root for the paired index-subsystem increment.
The output displays headline types, their executable domains and posts,
and each unproved semantic/environment premise used by those headlines.
This is a review aid; it does not assert any of the printed premises. -/

#check @Binary.Pair.Remove.remove_checked
#check @Binary.Pair.Remove.remove_simulation
#check @Binary.Pair.Replace.replace_checked
#check @Binary.Pair.Replace.replace_simulation
#check @Binary.Pair.IndexLookup.lookup_checked
#check @Binary.Pair.IndexLookup.lookup_simulation
#check @Binary.Pair.Sequence.sequence_checked

#print Binary.Pair.Remove.Pre
#print Binary.Pair.Replace.Pre
#print Binary.Pair.IndexLookup.Pre
#print Binary.Pair.Sequence.initialCheck
#print Binary.Pair.Sequence.Admissible
#print Binary.Pair.Sequence.AdmissibleSequence
#print Binary.Pair.Corresponds
#print Binary.Pair.Remove.Post
#print Binary.Pair.Replace.Post
#print Binary.Pair.IndexLookup.Post
#print Binary.Pair.Sequence.Ready
#print Binary.Pair.Sequence.Execute
#print Binary.Pair.Sequence.SequencePost
#print Binary.Pair.Sequence.EntryDomain
#print Binary.Pair.Sequence.Observed

#print Binary.TrustBase.AnchoredDecoderAgreement
#print Binary.TrustBase.IndexRemoveDecoderAgreement
#print Binary.TrustBase.IndexReplaceDecoderAgreement
#print Binary.TrustBase.TracePcContract
#print Binary.TrustBase.TraceCmp4Contract
#print Binary.TrustBase.TraceConstCmp4Contract
#print Binary.TrustBase.TraceConstCmp1Contract
#print Binary.TrustBase.BhEnableContract
#print Binary.TrustBase.ServiceReturns
#print Binary.TrustBase.SerializedEnvironment
#print Binary.TrustBase.ReturningCallPermissions
#print Binary.TrustBase.ReturningDomainPermissions
#print Binary.TrustBase.RunEnvironment

#print axioms Binary.Pair.Remove.remove_checked
#print axioms Binary.Pair.Remove.remove_simulation
#print axioms Binary.Pair.Replace.replace_checked
#print axioms Binary.Pair.Replace.replace_simulation
#print axioms Binary.Pair.IndexLookup.lookup_checked
#print axioms Binary.Pair.IndexLookup.lookup_simulation
#print axioms Binary.Pair.Sequence.sequence_checked
#print axioms Binary.Pair.Remove.Witness.check_linked
#print axioms Binary.Pair.Remove.Witness.check_unhashed
#print axioms Binary.Pair.Remove.Witness.executes
#print axioms Binary.Pair.Replace.Witness.check_linked
#print axioms Binary.Pair.Replace.Witness.check_unhashed
#print axioms Binary.Pair.Replace.Witness.executes
