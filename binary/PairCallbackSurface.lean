import PairCallbackAdequacy
import PairLookupFirstEnvironment
import PairRemoveFirstEnvironment
import PairReplaceFirstEnvironment
import PairSequenceFirstAdequacy
import PairInsertionSurface

/-! Shared image callbacks, first-return clients and explicitly broader insertion clients. -/

#check @Binary.Callback.pc_contract
#print axioms Binary.Callback.pc_contract
#check @Binary.Callback.cmp4_contract
#print axioms Binary.Callback.cmp4_contract
#check @Binary.Callback.const_cmp4_contract
#print axioms Binary.Callback.const_cmp4_contract
#check @Binary.Callback.const_cmp1_contract
#print axioms Binary.Callback.const_cmp1_contract
#check @Binary.Callback.bh_contract
#print axioms Binary.Callback.bh_contract
#check @Binary.Pair.IndexLookup.lookup_first_return
#print axioms Binary.Pair.IndexLookup.lookup_first_return
#check @Binary.Pair.Remove.remove_first_return
#print axioms Binary.Pair.Remove.remove_first_return
#check @Binary.Pair.Replace.replace_first_return
#print axioms Binary.Pair.Replace.replace_first_return
#check @Binary.Pair.Sequence.First.sequence_checked
#print axioms Binary.Pair.Sequence.First.sequence_checked
#check @Binary.Pair.Insert.insert_simulation_from_image
#print axioms Binary.Pair.Insert.insert_simulation_from_image
#check @Binary.Pair.Insert.insert_from_image
#print axioms Binary.Pair.Insert.insert_from_image
#check @Binary.Pair.InsertSequence.sequence_from_image
#print axioms Binary.Pair.InsertSequence.sequence_from_image
