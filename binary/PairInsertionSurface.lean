import PairSubsystemSurface
import PairInsertEnvironment
import PairInsertWitnessExecution
import PairInsertSequenceAdequacy

/-! Export root for insertion and retained-heap input-driven composition.
Service and environment contracts are hypotheses, not proved image facts. -/

#check @Binary.Pair.Insert.insert_checked
#check @Binary.Pair.Insert.insert_simulation
#check @Binary.Pair.InsertSequence.sequence_checked
#check @Binary.Pair.Insert.Witness.check
#check @Binary.Pair.Insert.Witness.executes

#print Binary.Pair.Insert.Pre
#print Binary.Pair.Insert.Post
#print Binary.Pair.InsertSequence.initialCheck
#print Binary.Pair.InsertSequence.Ready
#print Binary.Pair.InsertSequence.AdmissibleSequence
#print Binary.Pair.InsertSequence.SourceBoundaries
#print Binary.Pair.InsertSequence.Boundary
#print Binary.Pair.InsertSequence.Execute
#print Binary.Pair.InsertSequence.SequencePost
#print Binary.Pair.InsertSequence.EntryDomain

#print Binary.TrustBase.IndexInsertDecoderAgreement
#print Binary.TrustBase.RandomReady
#print Binary.TrustBase.RandomReturnContract
#print Binary.TrustBase.RandomInputCoupling
#print Binary.RandomProvider.Config
#print Binary.RandomProvider.check
#print Binary.RandomProvider.recording
#print Binary.RandomProvider.roleApart
#print Binary.RandomProvider.writesApart
#print Binary.RandomProvider.recordingGeometry

#print axioms Binary.Pair.Insert.insert_checked
#print axioms Binary.Pair.Insert.insert_simulation
#print axioms Binary.Pair.InsertSequence.sequence_checked
#print axioms Binary.Pair.Insert.Witness.check
#print axioms Binary.Pair.Insert.Witness.source_success
#print axioms Binary.Pair.Insert.Witness.executes
#print axioms Binary.RandomService.return_recorded
