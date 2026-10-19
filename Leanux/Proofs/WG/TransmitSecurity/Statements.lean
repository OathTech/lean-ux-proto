import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConsequencesAdmission
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConsequencesFrontier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConsequencesPartition
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConsequencesReceipts
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConsequencesSelectedAnchor
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConsequencesSelectedAnchorFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteNonDelete
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixContracts
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixHistory
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixQuiet
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixState
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecyclePacketChecked
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecyclePacketEnvironmentChecked
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecyclePacketEnvironmentFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecyclePacketEnvironmentSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecyclePacketSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterActors
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterBoundaryFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterControls
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterDispatch
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterDispatchAll
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterLifecycle
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterRouting
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerOuterSyscall
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxAuxiliaryFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTrafficEndpointFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTrafficFinishFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTrafficFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTrafficNativeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTrafficSections
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerClosed
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerCompanion
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerCompanionFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerDeleteFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerDeleteSyscall
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerHistoryFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerNative
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerAuxiliary
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerAuxiliaryEntry
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerConfigurationDeviceFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerConfigurationDeviceSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerControlFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerControls
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDeferred
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDeferredOuter
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDeferredOuterNative
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDeferredTimers
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecycleCuts
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecycleDelete
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecycleDestruct
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecycleGuard
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecyclePositive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerLifecycleStop
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollBoundaryFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollContext
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollContextFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollHistoryFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollNativeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollPhaseFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollSelection
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollSelectionFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxAdmissionFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxConsumption
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxConsumptionFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxDecryptFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxDecryptHistoryFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxIngressFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxOutcomeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerScheduler
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerSchedulerAtoms
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTransmit
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxEncryptFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxEncryptHistoryFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerInitialFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerOperations
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerAllowedIps
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerConfigurationAcquire
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerConfigurationCommand
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerConfigurationDeviceBoundary
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerConfigurationTail
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerConfigurationUpdate
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDeviceCreate
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDrain
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDumpCallers
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDumpCredits
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDumpCursor
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDumpDispatch
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerDumpSocket
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeArms
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeConsumers
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeCookie
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeDispatch
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeEndpoint
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeMaintenance
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeSend
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPollCallbackFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerReceiveTail
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerReceiveWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRemoval
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxEnqueueFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxFinishFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxPublicationFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTimerCallbacks
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTimerEnvironment
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTimerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTimerZero
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxCompletionFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxHistoryFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxStepFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerWork
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerWorkDispatch
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerWorkFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAdministrativeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAdministrativeSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDumpClosed
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDumpFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDumpSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteExecutionSources
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteIngressAllocated
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteIngressFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteIngressSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteOuterComposition
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductTx
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductTxHistory
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductTxNative
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductWork
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductWorkNative
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerAcquireFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerPhases
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxAllocationFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerRxSelectionFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTxFrames
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteAccounted
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteDead
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteTxBody
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteTxDispatch
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteTxFrontier
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteTxSelection
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteTxWorker
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteWorkerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCryptNative
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCryptSources
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDecryptFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDecryptSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDeferred
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDeferredFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDestructQuiescence
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDeviceCreation
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDeviceCreationFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteEncryptPublication
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteEncryptSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteEnvironment
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteEnvironmentFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteOuterNativeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductNapi
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductNapiFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetired
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerAccounting
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerCallbackFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerCreationFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHolderFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerSpine
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerSpineFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTransfers
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRing
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTraffic
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTrafficFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePollConcrete
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePollNapi
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePollSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteStackSource
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteDispose
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteFresh
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteFrontier
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompletePassive
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteRelease
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteSequence
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteWhole
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConfigurationClosed
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteNativeCalls
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteNoKey
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePollBase
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePollNative
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProduct
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReceiveConsumer
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReceiveFinish
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReceiveObserved
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReceiveTail
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerBoundary
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteScheduler
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSchedulerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSelectedFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSelectedSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSourceClosed
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteStaging
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSubmit
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTimerCallbacks
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTransmit
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTransmitCuts
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocatedCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocatedFixture
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocation
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocationFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConfigurationReady
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConfigurationTail
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteConfigurationUpdate
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDeviceConfiguration
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteFixtureSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteFrontChecked
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteFrontCheckpoint
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteFrontFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteFrontSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteKeepalive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRestore
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSavedSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSelected
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteClearWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteHandshakeWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSendDrain
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSendWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteLifecycleSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteHandshakeConsumers
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteHandshakeObserved
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePassive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSourceQuiet
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTimerQueue
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteTimerSource
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteAccounting
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteCleanup
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteHistory
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteRefusal
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteResult
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteSend
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteSendLoop
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteSocket
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationClosed
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryDeviceConfiguration
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteCreateChecked
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryAllocatedFixture
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationNative
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationReady
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryLifecycleComplete
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationErasure
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationUpdate
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryAllocatedFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryAllocatedCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDisposalChecked
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAdmissionChecked
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionWorkerContract
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionFreshQueued
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompletePurgeSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteOriginalRelease
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteNestedRelease
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySendWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryClearWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryHandshakeWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationTail
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryFixtureSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySavedSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryHandshakeObserved
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryCompleteCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryLifecycleSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteLedgerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteConverse
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryRoutingFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConsumerSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryPeerCreationFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySavedFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryControlFrames
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedDispose
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryZeroTimer
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationTxWorkerContract
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryRetired
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTimerCallbacks
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveTail
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryKeyObserved
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveFinish
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationTxSelectionObserved
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationDeadEntryContract
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedSend
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedRelease
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTransmitSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryEncryptSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryPurgeSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveObserved
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedFamily
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedAfterSocket
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedTimerFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationTransmitSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueueSource
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateRepaymentCompletion
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateEntryTail
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionIndexedFree
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionGeometry
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadyStaging
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryFront
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySelection
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryKeepaliveSource
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadySubmit
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadyRestore
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPeerReleaseFrontier
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPublicationRepayment
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionReleaseFinish
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationAdmissionFrontier
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionRemaining
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateTailContracts
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationQueueFrontier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalProvenanceFront
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalProvenanceOrder
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationHeldSource
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSoundAllocation
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSoundRestore
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateTailSource
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalSendSuffix
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionFrontOutcome
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationAllocationCarrier
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationKeepaliveCarrier
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationNativeDisposalCarrier
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReleaseCarrier
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestoreCarrier
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRoutingCarrier
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationStoppedTake
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionNative
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionOverflow
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestoreCompositionFromTake
import Leanux.Proofs.WG.AuthenticatedEffects.CompletionFirstTerminalSource
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationReceipts
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationInjectiveAllocation
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationDisposalReceipts
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationQueueFramesNative
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationQueueFramesTimers
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationTakeFacts
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationAllocationTotal
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationRestoreProjection
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationTrimTotal
import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalEncryptionFocus
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseReceiveContracts
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseAdmissionProjection
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseWorkerNeutral
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseWorkerFrames
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleasePollFrames
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpContracts
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpDispatchContracts
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpDispatchProjection

import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationXmitErrors
import Leanux.Proofs.WG.TransmitSecurity.HeaderLength
import Leanux.Proofs.WG.TransmitSecurity.CompletionAppendCut
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityInitialized
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityFocusedProduct
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityEffectsHistory
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityBank
import Leanux.Proofs.WG.TransmitSecurity.EmissionDispatchFrames
import Leanux.Proofs.WG.TransmitSecurity.EmissionCleanupFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedSocketFinal
import Leanux.Proofs.WG.TransmitSecurity.StagedConfiguration
import Leanux.Proofs.WG.TransmitSecurity.StagedTraffic
import Leanux.Proofs.WG.TransmitSecurity.StagedConfigurationFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedAllowedIpFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedDeferred
import Leanux.Proofs.WG.TransmitSecurity.StagedIngressFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedPeerCreationFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedScheduler
import Leanux.Proofs.WG.TransmitSecurity.StagedPoll
import Leanux.Proofs.WG.TransmitSecurity.StagedFocusedProduct
import Leanux.Proofs.WG.TransmitSecurity.StagedWorkerFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedStack
import Leanux.Proofs.WG.TransmitSecurity.StagedCounter
import Leanux.Proofs.WG.TransmitSecurity.StagedProduct
import Leanux.Proofs.WG.TransmitSecurity.StagedTimerTransport
import Leanux.Proofs.WG.TransmitSecurity.StagedNativeSupportFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedEffectsOrigins
import Leanux.Proofs.WG.TransmitSecurity.StagedSocketSendFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedAdmission
import Leanux.Proofs.WG.TransmitSecurity.StagedTrim
import Leanux.Proofs.WG.TransmitSecurity.StagedKeepaliveFinal
import Leanux.Proofs.WG.TransmitSecurity.StagedHandshakeFrames
import Leanux.Proofs.WG.TransmitSecurity.SocketCiphertextBinding
import Leanux.Proofs.WG.TransmitSecurity.CompletionOriginFinal
import Leanux.Proofs.WG.HandshakeSecurity.EncryptionNonceEncoding
import Leanux.Proofs.WG.TransmitSecurity.BatchPayloadFinal
import Leanux.Proofs.WG.TransmitSecurity.RoutingFinal
import Leanux.Proofs.WG.TransmitSecurity.NonceStagingSafety
import Leanux.Proofs.WG.TransmitSecurity.NonceInitialized
import Leanux.Proofs.WG.TransmitSecurity.NonceTimers
import Leanux.Proofs.WG.TransmitSecurity.NonceHandshakeSafety
import Leanux.Proofs.WG.TransmitSecurity.WireNonce
import Leanux.Proofs.WG.TransmitSecurity.EncryptBinding
import Leanux.Proofs.WG.TransmitSecurity.PacketAllocation
import Leanux.Proofs.WG.TransmitSecurity.PacketMaterialFrames
import Leanux.Proofs.WG.TransmitSecurity.WorkerEncryption
import Leanux.Proofs.WG.TransmitSecurity.WorkerOccurrences
import Leanux.Proofs.WG.TransmitSecurity.JournalResponderProjection
import Leanux.Proofs.WG.TransmitSecurity.JournalCompletionProjection
import Leanux.Proofs.WG.TransmitSecurity.JournalHandshakeProjection
import Leanux.Proofs.WG.TransmitSecurity.JournalSocketHistory
import Leanux.Proofs.WG.TransmitSecurity.CompletionEmission
import Leanux.Proofs.WG.TransmitSecurity.Rekey
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginDriverOuter
import Leanux.Proofs.WG.TransmitSecurity.ReservationEncryption
import Leanux.Proofs.WG.TransmitSecurity.EncryptionCompletion
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastPoll
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastStaging
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastReceive
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastTransmit
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastRxPoll
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastDecrypt
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastHandshake
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastDeviceConfiguration
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastTx
import Leanux.Proofs.WG.TransmitSecurity.EncryptionHistoryFinal
import Leanux.Proofs.WG.TransmitSecurity.ReservationAssignmentEncryption
import Leanux.Proofs.WG.TransmitSecurity.BatchWorker
import Leanux.Proofs.WG.TransmitSecurity.BatchNativeStaging
import Leanux.Proofs.WG.TransmitSecurity.ReservationBankEncryption
import Leanux.Proofs.WG.TransmitSecurity.BatchNativeTx
import Leanux.Proofs.WG.TransmitSecurity.BatchNativeInitialized
import Leanux.Proofs.WG.TransmitSecurity.BatchJournalFinal
import Leanux.Proofs.WG.TransmitSecurity.SocketJournalFinal
import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginFinal

/-! Campaign 3: initialized nonce safety and transmit source contracts.
Actual key-allocation identity, reservation, packet and wire nonce are joined.
Full transmit authorization and occurrence conservation remain separate. -/
namespace Leanux.Proofs.WG.TransmitSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- Security: the complete native staging path preserves every surviving
staged plaintext's source and retains the selected batch's original positions
when its queue is cleared. Rejection restores the original occurrences; allocation and queue
publication do not invent staged plaintext. The entry carrier is explicit;
initialized routing authorization and terminal conservation remain separate. -/
theorem native_staging_preserves_staged_origins (pid : PeerId) :
    Staged.Origins.StateSafe (Driver.stagingObserved AuthenticatedEffects.CausalJournal.hooks pid) :=
  Staged.Origins.staging_observed pid

/-- Security: one complete transmit invocation transports the actual route
admission through selection, nonce refusal, allocation and publication while
retaining staged origins. This assumes the entry carrier and does not assert
that every admitted occurrence has already reached a terminal disposition. -/
theorem native_transmit_preserves_staged_origins (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Staged.Origins.StateSafe
      (Driver.transmitObserved AuthenticatedEffects.CausalJournal.hooks family addr packets mtu) :=
  Staged.Origins.transmit_observed family addr packets mtu

/-- Security: keepalive staging preserves its canonical preparation origin
through the same complete send path as routed plaintext. Its entry carrier is
explicit, and causal authorization comes from the independent effect result. -/
theorem native_keepalive_send_preserves_staged_origins (pid : PeerId) :
    Staged.Origins.StateSafe (Driver.keepaliveObserved AuthenticatedEffects.CausalJournal.hooks pid) :=
  Staged.Origins.keepalive_observed_source pid

/-- Security: the actual routing receipt appends fresh packet positions to the
certified surviving staged queue. The explicit entry carrier remains required
until full initialized transport is proved; this is not disposition coverage. -/
theorem native_routing_preserves_staged_origins (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Staged.Origins.StateSafe (AuthenticatedEffects.CausalJournal.state (Journal.front family addr packets mtu)) :=
  Staged.Origins.routing_observed family addr packets mtu

/-- Security: keepalive preparation introduces one source-labelled occurrence
only on successful native allocation into an empty staged queue. The source
carrier at entry is explicit; causal authorization is a separate result. -/
theorem native_keepalive_preserves_staged_origins (pid : PeerId) :
    Staged.Origins.StateSafe (AuthenticatedEffects.CausalJournal.keepalivePrepare pid) :=
  Staged.Origins.keepalive_observed pid

/-- Security: current-key selection retains every saved plaintext occurrence's
prior source position while clearing its actual peer queue. This local native
contract assumes the staged-origin carrier at entry. -/
theorem native_selection_retains_staged_origins (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => Staged.Origins.Carrier h w) Staged.Origins.Safe
      (AuthenticatedEffects.CausalJournal.state (Journal.selection pid))
      (fun value h w _ => Staged.Origins.Carrier h w ∧ ∀ peer key,
        value = some (peer,key) → Staged.Origins.Saved h pid peer w) :=
  Staged.Origins.selection_observed pid

/-- Security: native restoration preserves the selected batch's original source
occurrences. It assumes the saved batch and empty peer queue at this source cut;
restoration itself creates no new plaintext occurrence or disposition. -/
theorem native_restore_retains_staged_origins (pid : PeerId) (peer : Peer) (r : WGRunWitness Unit)
    (valid : r.Valid (HandshakeSecurity.NonceRejection.restore pid peer.staged))
    (before : Staged.Origins.Inv history r.before)
    (saved : Staged.Origins.Saved history pid peer r.before) : Staged.Origins.Inv history r.after :=
  Staged.Origins.restore_origin pid peer r valid before saved

/-- Security: every actual TX completion entry has a selected head allocated
in its strict preceding final journal. Delayed completion effects therefore
retain an actual packet-allocation ancestor, including stopped prefixes.
This does not authenticate that ancestor or infer every member from the head. -/
theorem initialized_completion_allocation_origin (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List AuthenticatedEffects.CausalJournal.Event) (pid : PeerId) (items : List SkbId)
    (position : (runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2 =
      pre ++ AuthenticatedEffects.CausalJournal.Event.old (.disposition (.completion pid items)) :: post) :
    CompletionOrigin.Certificate (pre.filterMap AuthenticatedEffects.CausalJournal.old?) items :=
  PacketOrigins.final_completion trace placeholders pre post pid items position

/-- Security: recording every native staging increment preserves the original
success or Stop exactly; rejected batches cannot be hidden by an observer that
only records successful sends. This is source erasure, not initialized safety. -/
theorem original_staging_nonce_observer (pid : PeerId) :
    ErasesStatePrefix (Nonce.stagingObserved pid) (sendStagedPackets pid) :=
  Nonce.stagingObserved_erases pid

/-- Security: an original nonce increment cannot reuse an allocation already
in the journal, assuming the explicit sending-counter invariant at entry.
The updated invariant and failure-prefix journal are preserved; initialized
caller coverage is a separate obligation. -/
theorem original_nonce_reservation (slot : KeypairId) :
    StatePrefixEnsures (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup
      (Nonce.reserveObserved slot) (fun _ h w _ => Nonce.Inv (Nonce.view w) h) :=
  Nonce.reserveObserved_safe slot

/-- Security: the nonce observer refers to the actual get/increment operation;
adding its receipt changes neither the native outcome nor either native state. -/
theorem original_nonce_reservation_erases (slot : KeypairId) :
    ErasesStatePrefix (Nonce.reserveObserved slot) (Nonce.reserveNative slot) :=
  Nonce.reserveObserved_erases slot

/-- Security: a complete original staged-send invocation cannot repeat any
recorded nonce allocation under its allocation-stamped sending key, assuming
the explicit entry invariant. Queue refusal and later Stop retain allocations;
caller initialization and allocation-to-AEAD transport are separate obligations. -/
theorem original_staging_nonce_safety (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup
      (Nonce.stagingObserved pid) :=
  Nonce.stagingObserved_safe pid

/-- Security: native key creation cannot reset the nonce history of an existing
allocation identity. Its fresh global stamp preserves the supplied allocation
invariant even if a device-local slot is reused. This is normal-call preservation. -/
theorem original_creation_nonce_safety (peer : Option PeerId)
    (history : List Nonce.Allocation) :
    Framing.Preserves (fun w => Nonce.Inv (Nonce.view w) history) (keypairCreate peer) :=
  Nonce.create_preserves peer history

/-- Security: the real runner starts with an empty sending-allocation history
and no active key, for either fixture flag. This establishes initialization,
not preservation by all later runner operations. -/
theorem initialized_nonce_projection (net bare : Bool) :
    Nonce.Inv (Nonce.view (Runner.initialWG net bare)) [] := by
  rw [Nonce.initial_view]
  exact Nonce.initial 0

/-- Security: distinct admitted sending counters cannot collide after the
native 64-bit serialization used by AEAD. The actual admission bound is enough;
no unbounded-Nat-to-wire injectivity assumption is used. Packet provenance and
single-use transport to encryption remain separate obligations. -/
theorem original_admitted_nonce_encoding {n m : Nat}
    (hn : n < REJECT_AFTER_MESSAGES) (hm : m < REJECT_AFTER_MESSAGES)
    (same : counterNonce n = counterNonce m) : n = m :=
  admitted_aead_nonce_injective hn hm same

/-- Security: each native encryption invocation records at most one actual
AEAD result with its original packet, preparation and key read; the observer
preserves every success and Stop. This local source coverage does not establish
that the worker selects each admitted packet only once. -/
theorem original_encryption_receipts (slot : KeypairId) (pkt : DataPacket)
    (w : World) (h : List Encryption.Receipt) :
    ErasesPrefix (Encryption.observe Env.checksumHelp slot pkt)
      (encryptPacket Env.checksumHelp slot pkt) ∧
    ∃ suffix, (runPrefix (Encryption.observe Env.checksumHelp slot pkt) w h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix,
        r.slot = slot ∧ r.packet = pkt ∧ r.Valid Env.checksumHelp :=
  ⟨Encryption.observe_erases Env.checksumHelp slot pkt,
    Encryption.observe_receipts Env.checksumHelp slot pkt w h⟩

/-- Security: native encryption uses the entry-resident key in the selected
slot and the packet's assigned nonce for both header and AEAD. Allocation,
checksum and padding preparation cannot substitute a different key. The source
premise is actual encryption success; staging authorization and queue provenance
must still connect that slot and packet to their earlier selection. -/
theorem original_ciphertext_key_binding (slot : KeypairId) (pkt : DataPacket)
    (w v : World) (bytes : List UInt8)
    (success : (encryptPacket Env.checksumHelp slot pkt).run w = .ok (some bytes,v)) :
    ∃ (k : Keypair) (p : Encryption.Prepared), Encryption.keyAt w slot = some k ∧
      bytes = dataMessage k.remoteIndex pkt.nonce k.sending.key
        (p.inner.bytes ++ List.replicate p.padding 0) :=
  Encryption.original_ciphertext_binding slot pkt w v bytes success

/-- Security: the rekey observer records only the actual guarded request to
the native handshake-queue helper, retaining that request through a later Stop.
A request does not promise that the helper's timeout/dead/pending guards queue
or transmit a handshake. -/
theorem original_rekey_requests (pid : PeerId) (w : WGWorld) (a : Ambient)
    (h : List Rekey.Request) :
    ErasesStatePrefix (Rekey.observe pid) (keepKeyFresh pid) ∧
    ∃ suffix, (runWGPrefix (Rekey.observe pid) w a h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix, r.peer = pid ∧ r.Valid :=
  ⟨Rekey.observe_erases pid,Rekey.observe_receipts pid w a h⟩

/-- Security: a valid current sending key above the rekey count causes the
original freshness check to call the native handshake-queue helper. The exact
helper result or Stop is preserved; source-state lookup premises are explicit. -/
theorem original_rekey_count_request (pid : PeerId) (slot : KeypairId) (p : Peer) (k : Keypair)
    (w : WGWorld) (d : Device) (a : Ambient)
    (device : w.dev = some d) (peer : d.peers[pid]? = some p)
    (current : p.keypairCurrent = some slot) (key : d.keypairs[slot]? = some k)
    (valid : k.sending.isValid = true) (past : REKEY_AFTER_MESSAGES < k.sendingCounter) :
    ((keepKeyFresh pid).run w).run a =
      ((sendQueuedHandshakeInitiation pid false).run w).run (Rekey.countChecked a k) := by
  exact (Rekey.observe_erases pid w a []).symm.trans
    (congrArg Prod.fst (Rekey.count_request pid slot p k w d a [] device peer current key valid past))

/-- Security: when the count arm does not trigger, a valid current initiator
key whose actual recorded age test expires requests native handshake work.
The source clock-test run is explicit, so no unrecorded wall-clock or latency
assumption replaces the C's age check. -/
theorem original_rekey_age_request (pid : PeerId) (slot : KeypairId) (p : Peer) (k : Keypair)
    (w : WGWorld) (d : Device) (a b : Ambient)
    (device : w.dev = some d) (peer : d.peers[pid]? = some p)
    (current : p.keypairCurrent = some slot) (key : d.keypairs[slot]? = some k)
    (valid : k.sending.isValid = true) (count : k.sendingCounter ≤ REKEY_AFTER_MESSAGES)
    (initiator : k.iAmTheInitiator = true)
    (expired : ((branchExpired .freshExpired k.sending.birthdate REKEY_AFTER_TIME).run w).run
      (Rekey.ageEntry a k) = .ok ((true,w),b)) :
    ((keepKeyFresh pid).run w).run a =
      ((sendQueuedHandshakeInitiation pid false).run w).run (CounterWindow.record b .freshSend true) := by
  exact (Rekey.observe_erases pid w a []).symm.trans
    (congrArg Prod.fst (Rekey.age_request pid slot p k w d a b [] device peer current key valid count initiator expired))

/-- Security: original session establishment preserves all prior sending
nonce allocations while assigning a new global identity to its new key. Key
rotation and reference release cannot reset a surviving allocation's counter. -/
theorem original_session_nonce_safety (pid : PeerId) (history : List Nonce.Allocation) :
    Framing.Preserves (fun w => Nonce.Inv (Nonce.view w) history) (beginSession pid) :=
  Nonce.Frames.begin_session pid history

/-- Security: native keepalive sending records every staging allocation and
preserves nonce non-reuse from the explicit entry invariant, including allocation
failure and later Stop. The observer changes no native result or state. -/
theorem original_keepalive_nonce_safety (pid : PeerId) :
    ErasesStatePrefix (Nonce.keepaliveObserved pid) (sendKeepalive pid) ∧
    StatePrefixPreserves (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup
      (Nonce.keepaliveObserved pid) :=
  ⟨Nonce.keepaliveObserved_erases pid,Nonce.keepaliveObserved_safe pid⟩

/-- Security: the original transmit entry retains non-reuse across routing,
staging and final peer release, including refusal and Stop. Its entry invariant
is explicit; this caller contract is not initialized driver closure or a claim
that admitted packets have already reached AEAD. -/
theorem original_transmit_nonce_safety (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ErasesStatePrefix (Nonce.transmitObserved family addr packets mtu) (wgXmit family addr packets mtu) ∧
    StatePrefixPreserves (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup
      (Nonce.transmitObserved family addr packets mtu) :=
  ⟨Nonce.transmitObserved_erases family addr packets mtu,
    Nonce.transmitObserved_safe family addr packets mtu⟩

/-- Security: every original timer callback preserves sending nonce non-reuse
from the explicit entry invariant and records its actual keepalive allocations,
including before Stop. This callback claim does not assume a timer was due;
wheel selection and driver transport are separate obligations. -/
theorem original_timer_nonce_safety (pid : PeerId) (timer : PeerTimer) :
    ErasesStatePrefix (Nonce.timerObserved pid timer) (timerCallback pid timer) ∧
    StatePrefixPreserves (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup
      (Nonce.timerObserved pid timer) :=
  ⟨Nonce.timerObserved_erases pid timer,Nonce.timerObserved_safe pid timer⟩

/-- Security: the complete original handshake receive worker preserves sending
nonce non-reuse through actual session creation and keepalive staging, with
allocations retained before later Stop. The source observer is exact; the
entry invariant and remaining initialized driver coverage stay explicit. -/
theorem original_handshake_worker_nonce_safety :
    ErasesStatePrefix Nonce.Handshake.observed receiveStep ∧
    StatePrefixPreserves (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup
      Nonce.Handshake.observed :=
  ⟨Nonce.Handshake.erases,Nonce.Handshake.safe⟩


/-- Security: original data consumption cannot reuse a sending nonce when
confirmation releases staged packets. Exact source erasure retains allocations
before later receive failure; the incoming nonce invariant remains explicit. -/
theorem original_receive_nonce_safety (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    ErasesStatePrefix (Nonce.consumeObserved pid pkt ep) (consumeDataDone pid pkt ep) ∧
    StatePrefixPreserves (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup
      (Nonce.consumeObserved pid pkt ep) :=
  ⟨Nonce.consumeObserved_erases pid pkt ep,Nonce.consumeObserved_safe pid pkt ep⟩

/-- Security: the actual receive poll preserves sending nonce non-reuse,
including replies generated by the real IPv4 stack callback and every earlier
allocation before Stop. No callback-silence premise replaces those sends;
initialized driver transport of the entry invariant remains open. -/
theorem original_native_poll_nonce_safety (pid : PeerId) (budget : Nat) :
    ErasesPrefix (Nonce.nativePollObserved pid budget)
      (rxPoll pid budget (fun packets => packets.forM Env.deliverInner)) ∧
    PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup
      (Nonce.nativePollObserved pid budget) :=
  ⟨Nonce.nativePollObserved_erases pid budget,Nonce.nativePollObserved_safe pid budget⟩

/-- Security: actual softirq scheduling preserves the sending nonce history
through every selected receive poll and stack reply, including before Stop.
The explicit incoming invariant is not an initialized scheduler claim. -/
theorem original_softirq_nonce_safety :
    ErasesPrefix Nonce.softirqObserved Env.napiSoftirq ∧
    PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup Nonce.softirqObserved :=
  ⟨Nonce.softirqObserved_erases,Nonce.softirqObserved_safe⟩

/-- Security: direct inline polling preserves nonce non-reuse through the
same native poll and stack reply paths; the source placement records and
failed-prefix allocations remain unchanged. -/
theorem original_inline_poll_nonce_safety :
    ErasesPrefix Nonce.inlinePollObserved Env.pollScheduledInline ∧
    PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup Nonce.inlinePollObserved :=
  ⟨Nonce.inlinePollObserved_erases,Nonce.inlinePollObserved_safe⟩

/-- Security: an IRQ-exit receive poll cannot reset or reuse the sending nonce
history, including replies it causes. Actual placement selection is retained;
whole-run initialization remains a separate obligation. -/
theorem original_irq_exit_nonce_safety :
    ErasesPrefix Nonce.irqExitObserved Env.napiIrqExit ∧
    PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup Nonce.irqExitObserved :=
  ⟨Nonce.irqExitObserved_erases,Nonce.irqExitObserved_safe⟩

/-- Security: every committed iteration of the native crypt/receive scheduler
preserves sending nonce non-reuse, including the encryption-before-TX path,
NAPI callbacks and allocations before Stop. Consistency trials on copied states
emit no allocations. The incoming invariant and whole-run initialization remain
explicit; packet transport to AEAD is a separate obligation. -/
theorem original_scheduler_nonce_safety (stack : Option Worker) :
    ErasesPrefix (Nonce.scheduleObserved stack) (Env.schedule stack) ∧
    PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup
      (Nonce.scheduleObserved stack) :=
  ⟨Nonce.scheduleObserved_erases stack, Nonce.scheduleObserved_safe stack⟩

/-- Security: both actual wheel passes preserve the nonce allocation history
through selected timer callbacks, send/clear workers and crypt scheduling,
including allocations before Stop. Native bucket/order guards remain present;
this is preservation from the explicit incoming invariant, not eventual timer
progress or initialized packet-to-AEAD transport. -/
theorem original_timer_pass_nonce_safety (j : UInt64) :
    (ErasesPrefix (Nonce.timersObserved j) (Env.runTimers j) ∧
      PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup
        (Nonce.timersObserved j)) ∧
    (ErasesPrefix (Nonce.placeholderTimersObserved j) (Env.runTimersPlaceholder j) ∧
      PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup
        (Nonce.placeholderTimersObserved j)) :=
  ⟨⟨Nonce.timersObserved_erases j, Nonce.timersObserved_safe j⟩,
    ⟨Nonce.placeholderTimersObserved_erases j, Nonce.placeholderTimersObserved_safe j⟩⟩

/-- Fixture injection preserves the sending nonce journal through the actual
receive and deferred worker sequence; stopped prefixes cannot reuse a reservation. -/
theorem original_injection_nonce_safety (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    ErasesPrefix (Nonce.injectObserved family port msg tos ll dest) (Env.inject family port msg tos ll dest) ∧
    PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup
      (Nonce.injectObserved family port msg tos ll dest) :=
  ⟨Nonce.injectObserved_erases family port msg tos ll dest,
    Nonce.injectObserved_safe family port msg tos ll dest⟩

/-- Every native fixture batch retains nonce non-reuse through its actual
transmit, receive, inline poll and deferred callbacks, from the visible entry invariant. -/
theorem original_batch_nonce_safety (items : List Env.BatchItem) :
    ErasesPrefix (Nonce.batchObserved items) (Env.batch items) ∧
    PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup (Nonce.batchObserved items) :=
  ⟨Nonce.batchObserved_erases items,Nonce.batchObserved_safe items⟩

/-- Device configuration cannot reset a retained sending allocation's nonce
frontier; keepalive and staging callbacks append their actual reservations before Stop. -/
theorem original_configuration_nonce_safety (attrs : DeviceAttrs) :
    ErasesStatePrefix (Nonce.configDevice attrs) (wgSetDevice attrs) ∧
    StatePrefixPreserves (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup (Nonce.configDevice attrs) :=
  ⟨Nonce.configDevice_erases attrs,Nonce.configDevice_safe attrs⟩

/-- Bringing up the interface preserves nonce non-reuse through its actual
queued packets and keepalives; fixture routing never resets the sending frontier. -/
theorem original_interface_up_nonce_safety :
    ErasesPrefix Nonce.envUpObserved Env.wgUp ∧
    PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup Nonce.envUpObserved :=
  ⟨Nonce.envUpObserved_erases,Nonce.envUpObserved_safe⟩

/-- Security: every typed initialized Runner trace reserves each pair of key
allocation stamp and sending nonce at most once, including reservations in a
failed prefix. Actual fixture initialization discharges the entry invariant;
exact source erasure retains JSON and indexed Stop for either placeholder mode.
Connecting queued packet occurrences and AEAD invocations remains separate. -/
theorem initialized_nonce_reservations (trace : Runner.Trace) (placeholders : Bool) :
    ErasesOuter (Nonce.executeObserved trace placeholders) (Runner.executeTrace trace placeholders) ∧
    List.Nodup (runPrefixOuter (Nonce.executeObserved trace placeholders) []).2 :=
  ⟨Nonce.executeObserved_erases trace placeholders,Nonce.initialized_safe trace placeholders⟩

/-- Security: native batch allocation binds each returned packet ID to the
corresponding original full packet value, including peer, key slot and nonce.
The actual normal allocator run and present device are the only premises;
queue provenance and initialized occurrence conservation remain separate. -/
theorem original_tx_allocation_packet_binding (packets : List DataPacket)
    {w v : WGWorld} {d : Device} {a b : Ambient} {item : List SkbId}
    (device : w.dev = some d)
    (run : ((packets.mapM newTxSkb).run w).run a = .ok ((item,v),b)) :
    ∀ (n : Nat) packet, packets[n]? = some packet →
      ∃ id, item[n]? = some id ∧ Queues.TxDisposition.txPackets v id = some packet :=
  PacketAllocation.records packets device run

/-- Security: actual encryption and DEAD/CRYPTED publication cannot substitute
packet peer, key slot, nonce or original plaintext. The whole native batch tail
preserves those fields on normal return, including partial encryption failure;
this frame does not assert that a ring item was authorized or consumed once. -/
theorem original_encrypt_batch_material (item : Option (List SkbId)) :
    Leanux.Proofs.Framing.SameView (fun w : World => PacketMaterial.view w.wg)
      (Queues.RxWorkers.encryptStepTailSource item) :=
  PacketMaterial.encrypt_tail item

/-- Security: every recorded native worker AEAD is bound to the actual batch
head's selected key word and its own packet read, with valid native preparation
and key-read evidence. Exact erasure includes partial failure and Stop. This
source contract keeps queue provenance and one-time selection as separate obligations. -/
theorem original_encrypt_worker_packet_receipts (item : Option (List SkbId)) (w : World) :
    ErasesPrefix (WorkerEncryption.tail item) (Queues.RxWorkers.encryptStepTailSource item) ∧
    WorkerEncryption.Good (runPrefix (WorkerEncryption.tail item) w []).2 :=
  ⟨WorkerEncryption.tail_erases item,WorkerEncryption.tail_receipts item w⟩

/-- Security: reservations, allocated packet identities, ring selections, native
AEAD receipts and TX dispositions share one initialized execution chronology.
Its exact reservation projection is duplicate-free for every typed Runner trace
and both placeholder settings, including Stop; packet-to-reservation ownership
and one-time encryption still require the separate inventory transport. -/
theorem initialized_joint_transmit_reservations (trace : Runner.Trace) (placeholders : Bool) :
    ErasesOuter (Journal.execute trace placeholders) (Runner.executeTrace trace placeholders) ∧
    ProjectsOuter Journal.nonce? id (Journal.execute trace placeholders) (Nonce.executeObserved trace placeholders) ∧
    List.Nodup ((runPrefixOuter (Journal.execute trace placeholders) []).2.filterMap Journal.nonce?) :=
  ⟨Journal.execute_erases trace placeholders,Journal.execute_projects trace placeholders,
    Journal.initialized_reservations trace placeholders⟩

/-- Security: one selected batch cannot encrypt one packet twice when its IDs
are distinct; receipts follow a sublist of the selected packet order even on
Stop. Initialized selection uniqueness remains a separate phase invariant. -/
theorem original_encrypt_worker_occurrences (item : Option (List SkbId)) (w : World)
    (unique : (item.getD []).Nodup) :
    ((runPrefix (WorkerEncryption.tail item) w []).2.map WorkerEncryption.Receipt.id).Nodup ∧
      ((runPrefix (WorkerEncryption.tail item) w []).2.map WorkerEncryption.Receipt.id).Sublist (item.getD []) :=
  WorkerEncryption.tail_occurrences item w unique

/-- Security: the current-key selection, session creation and immediate
confirmation receipts belong to the same initialized execution as transport
reservations and AEAD receipts, including stopped prefixes. This exact internal
projection is the linkage needed by the separate responder-authorization proof. -/
theorem initialized_joint_responder_projection (trace : Runner.Trace) (placeholders : Bool) :
    ProjectsOuter Journal.responder? id (Journal.execute trace placeholders)
      (HandshakeSecurity.Responder.DriverCuts.execute trace placeholders) :=
  Journal.ResponderProjection.execute trace placeholders

/-- Security: each TX worker socket receipt records the actual packet read,
peer endpoint read and native IPv4/IPv6 socket call, even if later accounting
stops. This exact source observer does not establish prior AEAD ownership or
claim that a failed socket call emits a datagram. -/
theorem original_transmit_socket_receipts (pid : PeerId) (w : World) :
    ErasesPrefix (Completion.step pid) (liftWG (txStep pid)) ∧
    Completion.Good (runPrefix (Completion.step pid) w []).2 :=
  ⟨Completion.step_erases pid,Completion.step_receipts pid w⟩

/-- Security: the combined TX callback retains the same socket and disposition
receipts, in order and through Stop; native endpoint equality alone would not
justify this internal projection. Incoming socket validity remains explicit. -/
theorem original_joint_transmit_socket_projection (pid : PeerId) (w : World)
    (h : List Journal.Event) (incoming : Completion.Good (h.filterMap Journal.completion?)) :
    ProjectsPrefix Journal.completion? id (Journal.transmit pid) (Completion.step pid) ∧
    Completion.Good ((runPrefix (Journal.transmit pid) w h).2.filterMap Journal.completion?) :=
  ⟨Journal.transmit_completion_projection pid,Journal.transmit_socket_receipts pid w h incoming⟩

/-- Security: each handshake callback in every initialized combined execution
has a strictly earlier valid native authentication admission for its peer.
This covers the observed handshake callback sites; transport and delayed timer
or work causes require their separate carrier arguments. -/
theorem initialized_joint_handshake_causes (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List AuthenticatedEffects.HandshakeCausal.Event)
    (kind : AuthenticatedEffects.HandshakeCausal.Kind) (pid : PeerId)
    (position : (runPrefixOuter (Journal.execute trace placeholders) []).2.filterMap Journal.handshake? =
      pre ++ .callback kind pid :: post) :
    ∃ r ∈ AuthenticatedEffects.HandshakeCausal.roots pre, r.Valid ∧ r.ForPeer pid :=
  Journal.HandshakeProjection.callback_cause trace placeholders pre post kind pid position

/-- Security: in every initialized combined execution, each retained transport
socket receipt describes actual packet and peer reads and a native socket call.
That call appends at most one datagram, bound to its observed endpoint, bytes
and traffic class. Later Stop preserves the receipt. Prior AEAD authorization
and complete coverage of all egress still require the packet carrier argument. -/
theorem initialized_joint_socket_binding (trace : Runner.Trace) (placeholders : Bool)
    (r : Completion.SocketReceipt)
    (member : r ∈ (runPrefixOuter (Journal.execute trace placeholders) []).2.filterMap
      Journal.SocketHistory.socket?) :
    r.Valid ∧ AuthenticatedEffects.SocketEmission r.endpoint r.packet.value.bytes r.packet.value.ds
      r.socket.before.wg.sent r.socket.after.wg.sent := by
  have valid := Journal.SocketHistory.initialized trace placeholders r member
  exact ⟨valid,Completion.SocketReceipt.Valid.emission valid⟩

/-- Security: every surviving TX packet keeps an actual allocation certificate
when a batch is allocated. The certificate records the native input material,
returned packet ID and device epoch. The incoming resident carrier is explicit;
this does not yet bind the packet to a nonce reservation or routing decision. -/
theorem original_joint_allocation_origins (packets : List DataPacket) :
    PacketOrigins.StateSafe (Journal.allocate packets) :=
  PacketOrigins.allocate packets

/-- Security: each actual AEAD receipt produced by the worker has a matching
native allocation in the strict preceding journal prefix, even on later Stop.
The incoming packet-origin carrier remains explicit; no global nonce or
authorization claim is inferred from this local source contract. -/
theorem original_joint_encrypt_allocation_origins (item : Option (List SkbId)) :
    PacketOrigins.ProductSafe (Journal.encrypt item) :=
  PacketOrigins.encrypt item

/-- Security: native worker scheduling preserves strict earlier allocation
evidence for AEAD receipts, including NAPI-triggered replies and handshake
keepalives. The incoming resident-origin carrier is explicit; initialized
configuration and lifecycle transport remain a separate obligation. -/
theorem original_joint_scheduler_allocation_origins (stack : Option Worker) :
    PacketOrigins.ProductSafe (Driver.scheduleObserved Journal.hooks stack) :=
  PacketOrigins.schedule stack

/-- Security: actual timer dispatch and its delayed worker callbacks preserve
the same packet-origin evidence through later Stop. This establishes origin
transport under its incoming carrier, not timer-cause authentication. -/
theorem original_joint_timer_allocation_origins (bound : UInt64) :
    PacketOrigins.ProductSafe (Driver.timersObserved Journal.hooks bound) :=
  PacketOrigins.timers bound

/-- Security: each native worker AEAD in every initialized shared execution
has a valid receipt and a strictly earlier native packet allocation matching
its device epoch, packet ID and original material. The initial carrier and
all configuration/lifecycle transport are discharged, including later Stop.
Reservation linkage, route authorization and encryption non-reuse remain
separate obligations. -/
theorem initialized_joint_encryption_allocation_origin (trace : Runner.Trace)
    (placeholders : Bool) (pre post : List Journal.Event) (r : WorkerEncryption.Receipt)
    (position : (runPrefixOuter (Journal.execute trace placeholders) []).2 =
      pre ++ .encrypted r :: post) :
    r.Valid ∧ PacketOrigins.ReadOrigin pre r.id r.read :=
  PacketOrigins.initialized trace placeholders pre (.encrypted r) post position

/-- Security: every actual AEAD in the initialized shared execution uses a
below-limit packet nonce backed by a strictly earlier native reservation and
its allocation-stamped nonce event in this same journal, including later Stop.
No caller invariant is assumed. Key-material continuity and single consumption
of reservations at encryption remain separate obligations. -/
theorem initialized_joint_encryption_reservation (trace : Runner.Trace)
    (placeholders : Bool) (pre post : List Journal.Event) (r : WorkerEncryption.Receipt)
    (position : (runPrefixOuter (Journal.execute trace placeholders) []).2 =
      pre ++ .encrypted r :: post) :
    r.Valid ∧ r.cipher.packet.nonce < REJECT_AFTER_MESSAGES ∧
      ReservationHistory.Reserved pre r.read.value.keypair r.read.value.nonce := by
  obtain ⟨valid,bound,reserved⟩ := ReservationHistory.initialized_encryption trace placeholders pre post r position
  exact ⟨valid,by simpa only [valid.2.2.2.1] using bound,reserved⟩

/-- Security: normal completion of the native selected encryption tail marks
its batch head crypted or dead, so it is no longer an uncrypted candidate.
The source head equality is explicit. Global pending-alias exclusion and
historical encryption uniqueness remain separate obligations. -/
theorem original_encryption_tail_terminal (items : List SkbId) (first : SkbId)
    (head : items.head? = some first) :
    Framing.Hoare (Queues.RxWorkers.encryptStepTailSource (some items)) (fun _ => True)
      (fun _ w => EncryptionCompletion.Terminal first w.wg) :=
  EncryptionCompletion.native_tail items first head

/-- Security: the actual encryption worker cannot repeat an old packet
identity or one in its selected batch, including before later Stop. On normal
return all old and new encryption identities stay excluded from pending work.
Physical selection ownership and historical exclusion are explicit entry
premises; initialized global non-reuse is a separate obligation. -/
theorem original_encryption_history_exclusion
    (physical : RetirementSecurity.OccurrenceStack.Ready [] (items :: active) w.wg)
    (past : EncryptionPast.Inv (h.map WorkerEpochs.identity) (items :: active) (EncryptionPast.view w.wg)) :
    let execution := runPrefix (WorkerEncryption.tail (some items)) w h
    (execution.2.map WorkerEpochs.identity).Nodup ∧
      ∀ result v, execution.1 = .ok (result,v) →
        EncryptionPast.Inv (execution.2.map WorkerEpochs.identity) active (EncryptionPast.view v.wg) :=
  EncryptionPast.worker physical past

/-- Security: native ring selection transfers the selected live alias rather
than duplicating it. Exclusion of previously encrypted identities is retained
under the incoming physical ring and historical carrier. -/
theorem original_poll_history_exclusion
    (physical : Queues.TxDisposition.LiveFrontier.Physical w)
    (before : EncryptionPast.Inv past active (EncryptionPast.view w)) (a b : Ambient)
    (run : (Queues.TxRing.pollSource.run w).run a = .ok ((out,v),b)) :
    EncryptionPast.Inv past (out.toList ++ active) (EncryptionPast.view v) :=
  EncryptionPast.poll physical before a b run

/-- Security: actual packet allocation returns identities separate from all
prior encryptions represented by the incoming carrier. Abandoned work does
not reset the packet frontier; this is a native allocation cut, not initialized
nonce/key continuity or a global consumption theorem. -/
theorem original_allocation_history_exclusion (packets : List DataPacket)
    (before : EncryptionPast.Inv past active (EncryptionPast.view w)) (a b : Ambient)
    (run : ((packets.mapM newTxSkb).run w).run a = .ok ((items,v),b)) :
    EncryptionPast.Inv past active (EncryptionPast.view v) ∧
      EncryptionPast.Admissible past items (EncryptionPast.view v) :=
  EncryptionPast.allocate packets before a b run

/-- Security: native queue admission can only add a batch already separated
from historical encryptions, while each refusal preserves exclusion. The
physical ring and the batch's separation are explicit premises supplied by
separate native allocation and initialized ownership arguments. -/
theorem original_admission_history_exclusion (pid : PeerId) (items : List SkbId)
    (physical : Queues.TxDisposition.LiveFrontier.Physical w)
    (before : EncryptionPast.Inv past active (EncryptionPast.view w))
    (fresh : EncryptionPast.Admissible past items (EncryptionPast.view w)) (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid items).run w).run a = .ok ((result,v),b)) :
    EncryptionPast.Inv past active (EncryptionPast.view v) ∧
      EncryptionPast.Admissible past items (EncryptionPast.view v) :=
  EncryptionPast.enqueue pid items physical before fresh a b run

/-- Security: the complete native staged-send action preserves exclusion of
previously encrypted packet identities from pending work through all admission,
message-limit, no-key and refusal arms. The incoming physical/live bound and
historical carrier remain explicit; global initialized non-reuse and key-material
continuity are separate obligations. -/
theorem original_staged_send_history_exclusion (pid : PeerId) :
    Framing.Preserves (EncryptionPast.Ready past active) (sendStagedPackets pid) :=
  EncryptionPast.send pid

/-- Security: outgoing transmission, keepalive staging, every native timer
callback and RX polls with actual Stack/GRO replies cannot restore an already
encrypted identity to pending
work. These full-source preservation results keep the incoming physical/live
bound and historical exclusion explicit; initialized global non-reuse remains
an additional obligation. -/
theorem original_traffic_timer_history_exclusion :
    (∀ pid timer, Framing.Preserves (EncryptionPast.Ready past active) (timerCallback pid timer)) ∧
    (∀ pid pkt endpoint, Framing.Preserves (EncryptionPast.Ready past active)
      (WG.consumeDataDone pid pkt endpoint)) ∧
    (∀ family addr packets mtu, Framing.Preserves (EncryptionPast.Ready past active)
      (wgXmit family addr packets mtu)) ∧
    (∀ pid budget, Framing.Preserves (fun w : World => EncryptionPast.Ready past active w.wg)
      (rxPoll pid budget (fun packets => packets.forM Env.deliverInner))) :=
  ⟨EncryptionPast.timer,EncryptionPast.receive,EncryptionPast.transmit,EncryptionPast.stack_poll⟩

/-- Security: native ingress, decryption with real NAPI placements, full
handshake reception and queued handshake drains cannot reintroduce historical
encryption identities into pending TX work. The physical/live bound and incoming
historical carrier remain explicit; the initialized carrier and key-material
continuity are not assumed discharged by these normal-return contracts. -/
theorem original_ingress_handshake_history_exclusion :
    (∀ msg src, Framing.Preserves (EncryptionPast.Ready past active) (wgReceive msg src)) ∧
    Framing.Preserves (fun w : World => EncryptionPast.Ready past active w.wg)
      (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) ∧
    (∀ msg src, Framing.Preserves (EncryptionPast.Ready past active) (receiveHandshakePacket msg src)) ∧
    (∀ target, Framing.Preserves (EncryptionPast.Ready past active) (drainHandshakeSendWq target)) ∧
    (∀ pid, Framing.Preserves (EncryptionPast.Ready past active) (timersStop pid)) :=
  ⟨EncryptionPast.Ingress.receive,EncryptionPast.Decrypt.iteration,
    EncryptionPast.Handshake.receive,EncryptionPast.Maintenance.drain_send,
    EncryptionPast.Maintenance.timers_stop⟩

/-- Security: native peer/device configuration, lifecycle operations and TX
completion cannot make an old encrypted packet identity available as pending
encryption work. Fresh device epochs prevent numeric-ID reuse from conflating
allocations. Incoming physical/live bounds and historical exclusion remain
explicit; this does not assert the initialized global carrier or key continuity. -/
theorem original_configuration_lifecycle_history_exclusion :
    (∀ attrs, Framing.Preserves (EncryptionPast.Ready past active) (setPeerCmd attrs)) ∧
    (∀ attrs, Framing.Preserves (EncryptionPast.Ready past active) (wgSetDevice attrs)) ∧
    (∀ peer, Framing.Preserves (EncryptionPast.Ready past active) (peerRemove peer)) ∧
    Framing.Preserves (EncryptionPast.Ready past active) wgCreate ∧
    Framing.Preserves (EncryptionPast.Ready past active) wgOpen ∧
    Framing.Preserves (EncryptionPast.Ready past active) wgDown ∧
    Framing.Preserves (EncryptionPast.Ready past active) (wgDelete : WG.M Int) ∧
    (∀ pid, Framing.Preserves (fun w : World => EncryptionPast.Ready past active w.wg)
      (txIter pid (Env.condResched .txWorker))) :=
  ⟨EncryptionPast.PeerConfiguration.set_peer,EncryptionPast.DeviceConfiguration.set_device,
    EncryptionPast.Removal.remove_peer,EncryptionPast.DeviceFrames.create,
    EncryptionPast.DeviceLifecycle.device_open,EncryptionPast.Removal.down,
    EncryptionPast.DeviceLifecycle.device_delete_default,EncryptionPast.Tx.tx⟩

/-- Security: an actual transport-encryption receipt cannot reuse a packet
allocation identity in any initialized driver execution, including a stopped
prefix and both timer modes. The identity includes the device epoch, so device
recreation cannot alias old packet IDs. This derives physical ownership and
historical exclusion from initialization; key-material continuity remains a
separate requirement for the complete nonce-safety outcome. -/
theorem initialized_encryption_identity_nonreuse (trace : Runner.Trace) (placeholders : Bool) :
    EncryptionHistory.Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 ∧
    EncryptionHistory.Safe
      ((runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
        AuthenticatedEffects.CausalJournal.old?) :=
  ⟨EncryptionHistory.Scheduler.initialized trace placeholders,
    EncryptionHistory.final_initialized trace placeholders⟩

/-- Security: each native allocated batch assigns distinct reservation event
positions to its packets, all after every earlier allocation. Initialization
supplies this assignment through either timer mode and stopped prefixes; a
later batch cannot reuse a preceding batch's reservation credit. -/
theorem initialized_reservation_assignment (trace : Runner.Trace) (placeholders : Bool) :
    ReservationAssignments.Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 :=
  ReservationAssignments.initialized trace placeholders

/-- Security: every actual initialized AEAD has an exclusive allocation-stamped
native reservation token whose counter equals its packet nonce. No two AEAD
occurrences share an assigned token, including stopped executions and device
recreation. The same result holds in the exact final causal-journal projection.
Binding that allocation stamp to the resident AEAD key material remains separate. -/
theorem initialized_exclusive_encryption_reservations (trace : Runner.Trace) (placeholders : Bool) :
    ReservationAssignments.Exclusive (runPrefixOuter (Journal.execute trace placeholders) []).2 ∧
    ReservationAssignments.Exclusive
      ((runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
        AuthenticatedEffects.CausalJournal.old?) :=
  ⟨ReservationAssignments.initialized_exclusive trace placeholders,
    ReservationAssignments.final_exclusive trace placeholders⟩

/-- Security: every initialized native TX allocation batch has one peer and
one selected key slot throughout its packet arguments. This follows the actual
staging loop, including allocations before later Stop. Transport to the head
and per-packet reads of a selected encryption batch remains separate. -/
theorem initialized_batch_peer_key_alignment (trace : Runner.Trace) (placeholders : Bool) :
    BatchHistory.Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 :=
  BatchHistory.initialized trace placeholders

/-- Security: the native encryption worker's saved head key is the key slot
of every packet it encrypts, and head/packet peers agree, including receipts
before later Stop. Physical selection and resident-batch homogeneity are
explicit inputs; initialized transport of homogeneity remains to prove. -/
theorem original_selected_batch_key_alignment
    (before : BatchCoherence.Inv w.wg)
    (physical : RetirementSecurity.OccurrenceStack.Ready locals (items :: active) w.wg) :
    ∀ r ∈ (runPrefix (WorkerEncryption.tail (some items)) w []).2,
      r.head.value.keypair = r.read.value.keypair ∧ r.head.value.peer = r.read.value.peer ∧
      r.cipher.slot = r.read.value.keypair :=
  BatchWorker.selected before physical


/-- Mixed peer/key fields in an admitted batch could encrypt a packet under
its neighbour's key. Native staging preserves queued-batch alignment from
explicit physical ownership and prior alignment, across all refusal arms. -/
theorem original_staged_send_batch_alignment (pid : PeerId) :
    Framing.Preserves (BatchCoherence.Native.Coherent locals active) (sendStagedPackets pid) :=
  BatchCoherence.Native.send_coherent pid

/-- Reusing an allocation-stamped nonce reservation across actual AEAD calls
would break nonce safety. Any one certified assignment bank inherits exclusive
reservation use from initialized packet origins and encryption identity; bank
certification remains an explicit premise for a stronger material choice. -/
theorem initialized_certified_reservation_bank (trace : Runner.Trace) (placeholders : Bool)
    (bank : ReservationAssignments.Bank)
    (certified : ReservationAssignments.BankValid
      (runPrefixOuter (Journal.execute trace placeholders) []).2 bank) :
    ReservationAssignments.Bank.Exclusive bank
      (runPrefixOuter (Journal.execute trace placeholders) []).2 :=
  ReservationAssignments.Bank.exclusive certified
    (Journal.initialized_reservations trace placeholders)
    (PacketOrigins.initialized trace placeholders)
    (EncryptionHistory.Scheduler.initialized trace placeholders)

/-- A mixed-key batch could encrypt a packet under its neighbour's key.
The actual encrypt iteration preserves resident batch alignment across its
polled alias, NAPI callbacks, byte writes and publication. Physical ownership
and alignment are explicit entry premises; initialized transport is separate. -/
theorem original_encrypt_iteration_batch_alignment :
    Framing.Preserves (fun w : World => BatchCoherence.Native.Coherent locals active w.wg)
      (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) :=
  BatchCoherence.Encrypt.iteration

/-- Cross-peer or cross-key packet handling would violate transmit binding.
Actual native ingress, egress and TX disposal preserve the queued-batch
peer/key projection under the same explicit physical/alignment entry carrier.
This does not yet establish initialized routing or egress authorization. -/
theorem original_traffic_batch_alignment (family addr : Nat) (packets : List WG.Packet)
    (mtu : Nat) (msg : List UInt8) (src : SkbSource) (pid : PeerId) :
    Framing.Preserves (BatchCoherence.Native.Coherent locals active) (wgXmit family addr packets mtu) ∧
    Framing.Preserves (BatchCoherence.Native.Coherent locals active) (wgReceive msg src) ∧
    Framing.Preserves (BatchCoherence.Native.Coherent locals active) (txStep pid) :=
  ⟨BatchCoherence.Transmit.transmit family addr packets mtu,
    BatchCoherence.Receive.coherent msg src,BatchCoherence.Tx.step pid⟩

/-- A mixed-key queued batch could encrypt a packet under its neighbour's key.
Every normal initialized execution has aligned batches at each actual syscall
entry and the returned world, with no incoming alignment or callback premise.
Binding every internal encryption receipt, including stopped prefixes, remains
a separate shared-journal obligation. -/
theorem initialized_native_batch_alignment (trace : Runner.Trace) (placeholders : Bool)
    (run : runPrefixOuter (Queues.RxCredits.RunnerAccount.observed trace placeholders) [] =
      (.ok (result,w),h)) :
    BatchCoherence.Native.Coherent [] [] w.wg ∧
    ∀ index, index < trace.ops.size → BatchCoherence.Runner.OperationEntry trace placeholders index :=
  ⟨(BatchCoherence.Initialized.normal trace placeholders run).2,
    BatchCoherence.Initialized.entries trace placeholders run⟩

/-- A mixed-key batch could encrypt a packet under its neighbour's key.
Every initialized encryption receipt records the same key slot and peer at
the head and per-packet reads, and uses that packet's slot for AEAD. This
holds through stopped prefixes and the final causal journal, without incoming
batch or physical-ownership assumptions. Resident key-material continuity and
routing authorization remain separate obligations. -/
theorem initialized_encryption_batch_binding (trace : Runner.Trace) (placeholders : Bool) :
    BatchJournal.Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 ∧
    BatchJournal.Safe
      ((runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
        AuthenticatedEffects.CausalJournal.old?) :=
  ⟨BatchJournal.Scheduler.initialized trace placeholders,
    BatchJournal.final_initialized trace placeholders⟩

/-- A socket handoff for a different peer would violate transmit binding.
Every initialized transport socket receipt reads a packet whose stored peer is
the peer selected for that socket call. Actual cached queue selection supplies
the batch alignment; the result includes stopped prefixes and the exact final
causal journal, with no incoming alignment assumption. Ciphertext provenance,
historical routing linkage and complete conservation remain separate. -/
theorem initialized_socket_packet_peer_binding (trace : Runner.Trace) (placeholders : Bool) :
    SocketJournal.Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 ∧
    SocketJournal.Safe
      ((runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
        AuthenticatedEffects.CausalJournal.old?) :=
  ⟨SocketJournal.Scheduler.initialized trace placeholders,
    SocketJournal.final_initialized trace placeholders⟩

/-- Every nonempty socket payload in the initialized shared journal equals an
actual earlier AEAD result for the same packet identity and retained material.
This prevents substituting unrelated bytes after encryption; exclusion of empty
members in a CRYPTED batch is a separate native readiness obligation. The result
retains strict-prefix evidence through Stop and the exact final causal projection. -/
theorem initialized_socket_ciphertext_provenance (trace : Runner.Trace) (placeholders : Bool) :
    CiphertextOrigins.Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 ∧
    CiphertextOrigins.Safe
      ((runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
        AuthenticatedEffects.CausalJournal.old?) :=
  ⟨CiphertextOrigins.initialized trace placeholders,
    CiphertextOrigins.final_initialized trace placeholders⟩

/-- Security: recorded routing admissions cannot fabricate a destination-peer
selection; every initialized receipt is the actual native front through its
completed staged splice, including receipts retained before a later Stop. -/
theorem initialized_routing_admission_receipts (trace : Runner.Trace) (placeholders : Bool) :
    Journal.RoutingHistory.Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 ∧
    Journal.RoutingHistory.Safe
      ((runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
        AuthenticatedEffects.CausalJournal.old?) :=
  ⟨Journal.RoutingHistory.initialized trace placeholders,
    Journal.RoutingHistory.final_initialized trace placeholders⟩

/-- Security: a successful native admission selects the peer by the packet's
own destination, before the staged splice; subsequent configuration changes do
not replace that historical lookup. R3 supplies the separate flat-trie relation. -/
theorem recorded_admission_destination (receipt : Journal.RoutingHistory.Receipt)
    (valid : receipt.Valid) (pid : PeerId) (selected : receipt.run.value = .ok pid) :
    Packets.TxFrontCut receipt.family receipt.addr receipt.packets receipt.mtu
      receipt.run.before receipt.run.after receipt.run.ambientBefore receipt.run.ambientAfter pid ∧
    ∀ packet ∈ receipt.packets, Packets.destinationField receipt.family packet.bytes = receipt.addr :=
  receipt.selection valid pid selected


/-- Nonce reuse would break transport confidentiality and integrity. Every
initialized execution, including a stopped prefix, retains unique reservations,
unique actual key-allocation/AEAD nonce pairs, and unique serialized wire nonces.
Every ciphertext uses its packet's assigned header and AEAD counter below the
native rejection bound. No incoming carrier or campaign-2 hypothesis remains. -/
theorem initialized_nonce_safety (trace : Runner.Trace) (placeholders : Bool) :
    let h := (runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
      AuthenticatedEffects.CausalJournal.old?
    (h.filterMap Journal.nonce?).Nodup ∧
      ((h.filterMap Journal.encryption?).map HandshakeSecurity.EncryptionMaterial.token).Nodup ∧
      ((h.filterMap Journal.encryption?).map HandshakeSecurity.EncryptionMaterial.wireToken).Nodup ∧
      ∀ r ∈ h.filterMap Journal.encryption?, r.Valid ∧
        r.cipher.packet.nonce < REJECT_AFTER_MESSAGES ∧ HandshakeSecurity.EncryptionMaterial.Encoding r := by
  have material := HandshakeSecurity.EncryptionMaterial.final_initialized trace placeholders
  have encoding := HandshakeSecurity.EncryptionMaterial.final_encoding trace placeholders
  exact ⟨encoding.1,material.2.1,encoding.2.1,fun r member =>
    ⟨(material.1 r member).1,material.2.2 r member,encoding.2.2 r member⟩⟩

/-- Substitution or duplication during staging would detach ciphertext from
its intended packet. Each initialized allocation batch contains exactly the
plaintext sequence from its earlier native current-key selection, in order and
with duplicate occurrences retained, including before later Stop. This is the
staging-to-allocation link; routing origins and terminal conservation are separate. -/
theorem initialized_staged_plaintext_batches (trace : Runner.Trace) (placeholders : Bool) :
    BatchPayload.Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 ∧
      BatchPayload.Safe ((runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
        AuthenticatedEffects.CausalJournal.old?) :=
  ⟨BatchPayload.initialized trace placeholders,BatchPayload.final_initialized trace placeholders⟩


/-- An emitted payload without an earlier matching encryption could leak or
substitute data. Every actual initialized socket receipt is bound to its stored
packet peer and endpoint read, and its complete payload has a strictly earlier
AEAD certificate for the same packet allocation. Ready-batch initialization
removes the empty-cell exception, including before later Stop. Historical route
selection and exactly-once terminal disposition remain separate obligations. -/
theorem initialized_socket_encryption_binding (trace : Runner.Trace) (placeholders : Bool) :
    SocketCiphertext.Safe (runPrefixOuter (Journal.execute trace placeholders) []).2 ∧
      SocketCiphertext.Safe ((runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
        AuthenticatedEffects.CausalJournal.old?) :=
  ⟨SocketCiphertext.initialized trace placeholders,SocketCiphertext.final_initialized trace placeholders⟩


/-- Security: the native overflow arm cannot substitute or silently lose a
staged packet. It removes an ordered prefix, retains the exact suffix and adds
one drop count per removed position; equal plaintexts remain distinct positions.
The native call and its resident starting peer are explicit. -/
theorem native_staged_overflow_accounting (pid : PeerId) (r : WGRunWitness Unit)
    (valid : r.Valid (Lifetimes.xmitTrim pid)) :
    ∀ d p, r.before.dev = some d → d.peers[pid]? = some p →
      ∃ n, n ≤ p.staged.length ∧
        Staged.stagedAt r.after pid = some (p.internalId,p.staged.drop n) ∧
        Staged.dropped r.after = some (d.txDropped+n) ∧
        (∀ q, pid ≠ q → Staged.stagedAt r.after q = Staged.stagedAt r.before q) ∧
        p.staged.take n ++ p.staged.drop n = p.staged :=
  Staged.trim_exact pid r valid

/-- Security: routing admission cannot replace or reorder the supplied packet
sequence at its staged splice. Every initialized successful receipt contains the
exact MTU-normalized sequence after the queue's existing prefix. Its later
staging/allocation ancestry remains a separate transport obligation. -/
theorem initialized_routed_staged_sequence (trace : Runner.Trace) (placeholders : Bool)
    (receipt : Journal.RoutingHistory.Receipt)
    (member : receipt ∈ ((runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2.filterMap
      AuthenticatedEffects.CausalJournal.old?).filterMap Journal.RoutingHistory.routed?)
    (pid : PeerId) (selected : receipt.run.value = .ok pid) :
    ∃ stamp retained,
      Staged.stagedAt receipt.run.after pid =
        some (stamp,retained ++ receipt.packets.map (fun p => {p with mtu := receipt.mtu})) :=
  Staged.initialized_admission trace placeholders receipt member pid selected

/-- Security: native keepalive preparation can add only the canonical empty
packet to its caller's peer, using the actual MTU. It neither edits another
peer's staged queue nor changes drop accounting. This source contract supplies
no authentication or causal authorization merely from an empty payload. -/
theorem native_keepalive_preparation (pid : PeerId) (r : WGRunWitness Bool)
    (valid : r.Valid (RetirementSecurity.OccurrenceHandshake.keepalivePrepare pid)) :
    Staged.dropped r.after = Staged.dropped r.before ∧
      (∀ q, pid ≠ q → Staged.stagedAt r.after q = Staged.stagedAt r.before q) ∧
      ∃ stamp packets mtu,
        Staged.stagedAt r.before pid = some (stamp,packets) ∧
        r.before.dev.map Device.mtu = some mtu ∧
        (Staged.stagedAt r.after pid = some (stamp,packets) ∨
          (packets = [] ∧ r.value = true ∧ Staged.stagedAt r.after pid = some (stamp,[{mtu}]))) :=
  Staged.keepalive_projection pid r valid

/-- Security: every keepalive preparation recorded by the initialized execution
is an actual native call and can introduce only its caller's canonical empty
packet at the actual MTU. Other staged queues and drop accounting are unchanged.
A later Stop retains the receipt; causal authorization is a separate obligation. -/
theorem initialized_keepalive_preparation (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List AuthenticatedEffects.CausalJournal.Event) (pid : PeerId) (r : WGRunWitness Bool)
    (position : (runPrefixOuter (AuthenticatedEffects.CausalJournal.execute trace placeholders) []).2 =
      pre ++ AuthenticatedEffects.CausalJournal.Event.keepalivePrepared pid r :: post) :
    Staged.dropped r.after = Staged.dropped r.before ∧
      (∀ q, pid ≠ q → Staged.stagedAt r.after q = Staged.stagedAt r.before q) ∧
      ∃ stamp packets mtu,
        Staged.stagedAt r.before pid = some (stamp,packets) ∧
        r.before.dev.map Device.mtu = some mtu ∧
        (Staged.stagedAt r.after pid = some (stamp,packets) ∨
          (packets = [] ∧ r.value = true ∧ Staged.stagedAt r.after pid = some (stamp,[{mtu}]))) :=
  Staged.initialized_keepalive_preparation trace placeholders pre post pid r position


/-- Handshake processing preserves the staged packets' exact routing or
keepalive occurrences; a local incoming carrier is explicit until initialized
runner transport is closed. Authentication is proved separately. -/
theorem native_handshake_preserves_staged_origins :
    Staged.Origins.StateSafe (Driver.handshakeObserved AuthenticatedEffects.CausalJournal.hooks) :=
  Staged.Origins.handshake_observed

/-- Receive completion preserves staged occurrence origins through actual
confirmation and staging, so it cannot invent a staged packet's history.
This native contract has the local staged carrier as its entry premise. -/
theorem native_receive_preserves_staged_origins (pid : PeerId) (packet : RxPacket) (endpoint : Endpoint) :
    Staged.Origins.StateSafe
      (Driver.consumeObserved AuthenticatedEffects.CausalJournal.hooks pid packet endpoint) :=
  Staged.Origins.consume_observed pid packet endpoint

/-- Native handshake send work retains staged origins while releasing its
actual references; this local frame does not assert initialized conservation. -/
theorem native_send_work_preserves_staged_origins (pid : PeerId) :
    Staged.Origins.StateSafe (AuthenticatedEffects.CausalJournal.flushedSend pid) :=
  Staged.Origins.flushed_send_observed pid

/-- Timer callbacks retain exact staged origins and use the actual keepalive
preparation for any new packet. Timer authorization is a separate outcome;
the incoming staged carrier remains explicit in this source contract. -/
theorem native_timers_preserve_staged_origins (pid : PeerId) (timer : PeerTimer) :
    Staged.Origins.StateSafe (AuthenticatedEffects.TimerEffects.timerWith
      AuthenticatedEffects.CausalJournal.effects
      (Driver.keepaliveObserved AuthenticatedEffects.CausalJournal.hooks) pid timer) :=
  Staged.Origins.timer _ Staged.Origins.keepalive_observed_source pid timer

/-- Native NAPI polling retains each selected packet's earlier staged origin,
including stopped histories. The incoming positional carrier is explicit;
this local contract does not assume that packet values identify occurrences. -/
theorem native_napi_preserves_staged_origins (pid : PeerId) (budget : Nat) :
    Staged.Origins.ProductSafe
      (Driver.nativePollObserved AuthenticatedEffects.CausalJournal.hooks pid budget) :=
  Staged.Origins.native_poll pid budget

/-- Every actual scheduled packet worker retains the selected packets' staged
origins, through encryption, authenticated receive and TX completion. This
source contract retains its incoming carrier until initialized outer closure. -/
theorem native_scheduler_preserves_staged_origins (stack : Option Worker) :
    Staged.Origins.ProductSafe (Driver.scheduleObserved AuthenticatedEffects.CausalJournal.hooks stack) :=
  Staged.Origins.schedule stack


open AuthenticatedEffects HandshakeSecurity Staged.Origins

/-- Security: every initialized native staged selection retains ordered, distinct
prior routing or keepalive occurrences for its own peer allocation, including
before Stop. No incoming carrier is assumed. Cross-allocation consumption and
pending/terminal conservation are separate obligations. -/
theorem initialized_staged_selection_origins (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 :=
  Staged.Origins.initialized trace placeholders

/-- Security: every initialized allocation preserves the exact ordered staged
plaintexts and their prior routing or keepalive positions for the selected peer.
Duplicate payloads retain distinct positions within the batch. This does not
yet establish disjoint ticket consumption between separate allocations. -/
theorem initialized_allocated_staged_occurrences (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (packets : List DataPacket)
    (allocation : WGRunWitness (List SkbId))
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      pre ++ .old (.allocated packets allocation) :: post) :
    allocation.Valid (packets.mapM newTxSkb) ∧
      ∃ pid peer slot selection generation,
        CausalJournal.Event.old (.responder (.selected pid selection)) ∈ pre ∧
        selection.Valid (Responder.selectionPrefix pid) ∧
        selection.value = some (peer,some slot) ∧
        Packets.epoch selection.before = some generation ∧
        Batch pre generation pid peer.internalId (packets.map DataPacket.plaintext) ∧
        BatchPayload.Shape pid slot peer.staged packets :=
  Staged.Origins.initialized_allocation trace placeholders pre post packets allocation position

/-- Security: every initialized AEAD uses plaintext with an earlier native
routing or keepalive occurrence for the same packet peer. The conclusion holds
before later Stop without an incoming carrier; terminal conservation is separate. -/
theorem initialized_encrypted_plaintext_origin (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (r : WorkerEncryption.Receipt)
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      pre ++ .old (.encrypted r) :: post) :
    r.Valid ∧ ∃ generation stamp ticket,
      Born pre generation r.read.value.peer stamp ticket r.read.value.plaintext :=
  Staged.Origins.initialized_encryption trace placeholders pre post r position

/-- Security: every initialized transport socket receipt binds the actual
endpoint and emitted bytes to an earlier AEAD and its own earlier staged
plaintext origin. The selected current-slot allocation and sending core are
bound historically. The actual key at allocation is owned by the socket peer,
and its sending core matches the AEAD key even after owner clearing. Converse
coverage of all emissions and exactly-once conservation remain separate. -/
theorem initialized_socket_route_key_core_and_endpoint (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List CausalJournal.Event) (r : Completion.SocketReceipt)
    (position : (runPrefixOuter (CausalJournal.execute trace placeholders) []).2 =
      pre ++ .old (.socket r) :: post) :
    r.Valid ∧ r.packet.value.peer = r.pid ∧
      SocketEmission r.endpoint r.packet.value.bytes r.packet.value.ds
        r.socket.before.wg.sent r.socket.after.wg.sent ∧
      ∃ cipher : WorkerEncryption.Receipt,
        CausalJournal.Event.old (.encrypted cipher) ∈ pre ∧ cipher.Valid ∧
        cipher.read.value.peer = r.pid ∧
        r.packet.value.bytes = cipher.cipher.ciphertext ∧
        AllocationOwner.Historical (pre.filterMap CausalJournal.old?) cipher ∧
        AllocationSelection.Earlier (pre.filterMap CausalJournal.old?) r.pid r.packet.value.keypair
          (Responder.keyCore cipher.cipher.keyRead.value) ∧
        ∃ generation stamp ticket, Born pre generation r.pid stamp ticket r.packet.value.plaintext :=
  Staged.Origins.initialized_socket trace placeholders pre post r position

/-- Security: a native birth ticket cannot identify two different peers,
peer allocations, device epochs or plaintexts. The actual journal position
and packet ordinal identify the occurrence; equal payloads do not. Preventing
repeat consumption of the same ticket remains a separate obligation. -/
theorem staged_birth_ticket_identity
    (first : Staged.Origins.Born history generation pid stamp ticket packet)
    (second : Staged.Origins.Born history otherGeneration otherPid otherStamp ticket otherPacket) :
    generation = otherGeneration ∧ pid = otherPid ∧ stamp = otherStamp ∧ packet = otherPacket :=
  first.unique second

/-- Security: one staged birth ticket cannot fund two allocation positions
in a bank carrying the unconsumed-credit invariant. BankValid is an explicit
premise here; the initialized theorem below discharges it for the actual
runner. Complete terminal accounting remains a separate obligation. -/
theorem staged_available_ticket_unique
    {history : List CausalJournal.Event} {bank : Staged.Availability.Bank}
    {firstIndex secondIndex leftIndex rightIndex : Nat} {ticket : Staged.Origins.Ticket}
    {firstPackets secondPackets : List DataPacket}
    {firstRun secondRun : WGRunWitness (List SkbId)}
    (valid : Staged.Availability.BankValid history bank)
    (first : history[firstIndex]? = some (.old (.allocated firstPackets firstRun)))
    (second : history[secondIndex]? = some (.old (.allocated secondPackets secondRun)))
    (left : (bank firstIndex)[leftIndex]? = some ticket)
    (right : (bank secondIndex)[rightIndex]? = some ticket) :
    firstIndex = secondIndex ∧ leftIndex = rightIndex :=
  Staged.Availability.bank_ticket_injective valid first second left right

/-- Security: quiet native syscalls cannot emit an unrecorded datagram or
silently remove a pending one. This preserves the actual send buffer; active
traffic, up/down and worker callbacks use their separate observed paths. -/
theorem native_quiet_dispatch_preserves_sent_buffer (call : Syscall)
    (retained : Lifetimes.DispatchRetained call) (notUp : call ≠ .wgUp) (notDown : call ≠ .wgDown) :
    Framing.SameView EmissionOuter.Sent (Leanux.dispatch call) :=
  EmissionDispatch.quiet call retained notUp notDown

/-- Security: namespace cleanup cannot emit an unrecorded datagram or lose
an already pending send-buffer occurrence while changing sockets and routes.
Any active send callback is accounted for separately at its native source. -/
theorem native_namespace_cleanup_preserves_sent_buffer :
    Framing.SameView EmissionOuter.Sent Env.netnsCleanup :=
  EmissionCleanup.env_cleanup

/-- Security: native staging consumes an existing live birth credit only at
its actual allocation; no-key and counter-limit exits restore the saved
credits. This source contract keeps its incoming availability carrier explicit;
the initialized theorem below discharges that carrier from boot. Terminal
completeness remains a separate obligation. -/
theorem native_staging_preserves_available_births (pid : PeerId) :
    Staged.Availability.StateSafe (Driver.stagingObserved CausalJournal.hooks pid) :=
  Staged.Availability.staging_observed pid

/-- Security: accepted routing and keepalive creation introduce fresh birth
credits before native staging consumes them. This is the actual transmit
source with an explicit incoming availability carrier. -/
theorem native_transmit_preserves_available_births (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Staged.Availability.StateSafe (Driver.transmitObserved CausalJournal.hooks family addr packets mtu) :=
  Staged.Availability.transmit_observed family addr packets mtu

/-- Security: each actual transport allocation in the initialized native
runner consumes an ordered bank of live staging credits. Initialization
supplies the bank invariant, including histories retained before Stop;
there is no incoming carrier or campaign-2 hypothesis. This does not classify
every disposal or establish terminal completeness. -/
theorem initialized_available_birth_bank (trace : Runner.Trace) (placeholders : Bool) :
    Staged.Availability.BankValid (runPrefixOuter (CausalJournal.execute trace placeholders) []).2
      (Staged.Availability.bank (runPrefixOuter (CausalJournal.execute trace placeholders) []).2) :=
  Staged.Availability.bank_valid (Staged.Availability.initialized trace placeholders)

/-- Security: one routing/keepalive birth occurrence cannot supply two
transport packet allocation positions in an initialized native run, even
with equal payloads or a later Stop. The bank comes from that same execution;
no reachability, successful-return or input-invariant premise is assumed. -/
theorem initialized_available_birth_unique (trace : Runner.Trace) (placeholders : Bool)
    (history : List CausalJournal.Event)
    (execution : history = (runPrefixOuter (CausalJournal.execute trace placeholders) []).2)
    {firstIndex secondIndex leftIndex rightIndex : Nat} {ticket : Staged.Origins.Ticket}
    {firstPackets secondPackets : List DataPacket}
    {firstRun secondRun : WGRunWitness (List SkbId)}
    (first : history[firstIndex]? = some (.old (.allocated firstPackets firstRun)))
    (second : history[secondIndex]? = some (.old (.allocated secondPackets secondRun)))
    (left : (Staged.Availability.bank history firstIndex)[leftIndex]? = some ticket)
    (right : (Staged.Availability.bank history secondIndex)[rightIndex]? = some ticket) :
    firstIndex = secondIndex ∧ leftIndex = rightIndex := by
  subst history
  exact Staged.Availability.bank_ticket_injective
    (initialized_available_birth_bank trace placeholders) first second left right


/-- Security: native header admission fixes the exact initiation, response and
cookie widths. Later cookie amplification claims must derive this acceptance
for the same input; a message tag alone does not establish its size. -/
theorem native_header_acceptance_has_wire_width (msg : List UInt8)
    (w v : WGWorld) (a b : Ambient)
    (run : ((prepareSkbHeader msg).run w).run a = .ok ((true,v),b)) :
    HeaderLength.Valid msg := HeaderLength.prepared msg w v a b run

/-- Security: every transport socket that reaches its native datagram append
produces a receipt at that occurrence, retained before every later continuation
event even on Stop. The actual pre-append source execution is explicit; this
local converse does not assume that a containing worker returns successfully. -/
theorem transport_append_cannot_lose_receipt (pid : PeerId) (id : SkbId)
    (packet : RunWitness DataPacket) (peer : RunWitness Peer) (ipv4 : Bool)
    (w : World) (u : WGWorld) (b : Ambient) (history : List Completion.Event)
    (datagram : SentDatagram)
    (front : (((Completion.socketArgs pid packet peer ipv4).beforeAppend).run w.wg).run w.ambient =
      .ok ((.ok datagram,u),b))
    (next : Int → PrefixM Completion.Event α) (appends : ∀ value, Appends (next value)) :
    let v := {w with wg := {u with sent := u.sent ++ [datagram]},ambient := b}
    ∃ middle suffix, (runPrefix (Completion.socket pid id packet peer ipv4 >>= next) w history).2 =
      (history ++ middle) ++ .socket ⟨pid,id,packet,peer,ipv4,⟨0,w,v⟩⟩ :: suffix :=
    Completion.socket_append_retained pid id packet peer ipv4 w u b history datagram front next appends

/-- Security: each refused original transmit invocation returns one named
errno and charges the device error counter exactly once, independently of the
number of supplied GSO segments. The refusal is the same native front cut;
a successful splice or a stopped send tail is not classified as refusal. -/
theorem original_transmit_refusal_charged_once (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (r : WGRunWitness Int) (run : r.Valid (wgXmit family addr packets mtu))
    (refused : r.value ≠ 0) :
    (r.value = -EPROTONOSUPPORT ∨ r.value = -ENOKEY ∨
      r.value = -EDESTADDRREQ ∨ r.value = -ENOMEM) ∧
    HandshakeSecurity.StagedConservation.Front.errors r.after =
      (HandshakeSecurity.StagedConservation.Front.errors r.before).map (· + 1) ∧
    ((Packets.txFront family addr packets mtu).run r.before).run r.ambientBefore =
      .ok ((.error r.value,r.after),r.ambientAfter) :=
  HandshakeSecurity.StagedConservation.Front.xmit_refusal family addr packets mtu r run refused

section
open Staged.Obligations Staged.Origins
variable {births : List Staged.Origins.Ticket}

/-- Security: the actual full staged purge settles every incoming queue ticket
at its own counted purge receipt, retains every ledger identity and prior
terminal, and charges exactly the removed ticket count. The incoming fixed
ledger and native queue invariant remain explicit; initialized closure is open. -/
theorem native_purge_preserves_fixed_obligations (pid : PeerId) (r : WGRunWitness Unit)
    (run : r.Valid (purgeStagedPackets pid))
    (valid : Valid births ledger) (before : QueueInv history ledger r.before)
    (epoch : Packets.epoch r.before = some generation) :
    ∃ stamp after,
      Staged.Obligations.Step ledger after ∧ Valid births after ∧
      QueueInv (history ++ [.stagedDisposal (.purge pid r)]) after r.after ∧
      (∀ ticket ∈ pendingAt (.staged generation pid stamp) ledger,
        (ticket,Status.terminal (.counted history.length .purge)) ∈ after) ∧
      (∃ count, Staged.dropped r.before = some count ∧ Staged.dropped r.after =
        some (count+(pendingAt (.staged generation pid stamp) ledger).length)) :=
  Staged.Obligations.purge_receipt pid r run valid before epoch

/-- Security: final peer release settles every staged obligation at the actual
counted erase receipt, without losing it when the peer disappears. Its later
native cleanup may stop. This local contract exposes its incoming ledger,
queue invariant and native completed cut; it is not whole-run conservation. -/
theorem native_final_release_preserves_fixed_obligations (peer : Option PeerId)
    (r : WGRunWitness (Option (PeerId × Peer)))
    (run : r.Valid (HandshakeSecurity.StagedDisposal.releaseCut peer))
    (released : r.value = some (pid,p))
    (valid : Valid births ledger) (before : QueueInv history ledger r.before)
    (epoch : Packets.epoch r.before = some generation) :
    ∃ after,
      Staged.Obligations.Step ledger after ∧ Valid births after ∧
      QueueInv (history ++ [.stagedDisposal (.release peer r)]) after r.after ∧
      (∀ ticket ∈ pendingAt (.staged generation pid p.internalId) ledger,
        (ticket,Status.terminal (.counted history.length .finalRelease)) ∈ after) ∧
      (∃ count, Staged.dropped r.before = some count ∧ Staged.dropped r.after =
        some (count+(pendingAt (.staged generation pid p.internalId) ledger).length)) :=
  Staged.Obligations.release_receipt peer r run released valid before epoch

end

end Leanux.Proofs.WG.TransmitSecurity
