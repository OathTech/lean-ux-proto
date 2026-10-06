/-!
# C decision points

One constructor per C choice point on the modeled paths of the configured
Linux 6.12.110 source. The mirror records `⟨decision, outcome⟩` at the point
where the C evaluates the condition, in the C's order.

Each decision names its source site and the spans of source lines that run
only when the outcome is true (`whenTrue`) or only when it is false
(`whenFalse`). The check derives KCOV witnesses from these spans: the lines in
a span that own an instrumentation point in the built kernel. A reported
outcome must cover at least one of its span's witnesses, and the opposite
span's witnesses must stay uncovered. An empty span, or one without
instrumentation, makes that outcome unobservable by construction. Spans are
source facts, reviewed against the C; they are never fitted to coverage.

Short-circuit operands are separate decisions. When an operand shares its
line with the next operand (`a || b` on one line), its outcome spans are left
empty rather than borrowing lines that another operand also reaches.
-/

namespace Leanux

inductive Decision where
  -- fs/eventfd.c
  | eventfdFreeCtxHasId | krefPutLast
  | refcountSubPositive | refcountSubToZero | refcountSubNonpositive | refcountSubUnderflow | ctxDoReadSemaphore | ctxDoReadCountNonzero
  | eventfdReadShort | eventfdReadEmpty | eventfdReadNonblock | eventfdReadNowait
  | eventfdReadWaitqueueActive | eventfdReadCopyFault
  | eventfdWriteWrongSize | eventfdWriteCopyFault | eventfdWriteReserved | eventfdWriteFits
  | eventfdWriteBlocking | eventfdWriteResPositive | eventfdWriteWaitqueueActive
  | doEventfdInvalidFlags | doEventfdNoMem | doEventfdFdError | doEventfdFileError
  -- fs/file_table.c, fs/internal.h, include/linux/fs.h
  | fileFreeAccounted | fileFreeBacking | allocEmptyFileOverMax | allocEmptyFileNotCapable | allocEmptyFileNoMem
  | iocbFlagsAppend | iocbFlagsDirect | iocbFlagsDsync | iocbFlagsSync
  | fileInitPathLlseek | fileInitPathModeRead | fileInitPathHasRead | fileInitPathHasReadIter
  | fileInitPathModeWrite | fileInitPathHasWrite | fileInitPathHasWriteIter | fileInitPathReadOnly
  | allocFileOk | allocPathPseudoFail | allocFilePseudoErr
  | putFileAccessReadOnly | putFileAccessWriter
  | fputFinalNotOpened | eventpollReleaseLinked | fputFinalFasync | fputFinalRelease
  | fputFinalCharDevice | fputFinalHasCdev | fputFinalNotPath
  | fileOwnerRelease | fputFinalNeedUnmount
  | fputLast | fputNotOpened | fputInInterrupt | fputKthread | fputTaskWorkAddFailed | fputSyncLast
  -- fs/open.c
  | filpFlushCountZero | filpFlushHasFlush | filpFlushNotPath | closeNoFile
  | closeRestartSys | closeRestartNoIntr | closeRestartNoHand | closeRestartBlock
  -- fs/file.c, include/linux/file.h
  | clearCloexecWasSet | setOpenFdFullWord | findNextFdAllFull | findNextFdSkipFullWords
  | expandFilesFits | expandFilesOverNrOpen | expandFilesResizeInProgress
  | allocFdtableOverNrOpen | allocFdtableBelowWanted | allocFdtableOverIntMax | allocFdtableNoMem
  | allocFdtableFdArrayNoMem | allocFdtableBitmapNoMem | copyFdtableShrink
  | expandFdtableShared | expandFdtableAllocError | expandFdtableBugNr | expandFdtableFreeOld
  | allocFdBelowNextFd | allocFdSearch | allocFdLimit | allocFdExpandError | allocFdExpanded
  | allocFdUpdateNextFd | allocFdCloexec | allocFdSlotNotNull | putUnusedFdLowerNextFd
  | fdInstallBacking | fdInstallResizeInProgress | fdInstallSlotBusy
  | closeFdOutOfRange | closeFdFound
  | getFileFromZero | doDup2NoTofree | doDup2FdOpen | doDup2Cloexec | doDup2Replace
  | dup3InvalidFlags | dup3Equal | dup3TargetLimit | dup3NoFile | dup3ExpandError | dup3ExpandEmfile
  | fgetRcuNoFile | fgetRcuIncNotZeroFailed | fgetRcuEntryChanged | fgetRcuTableChanged | fgetRcuMasked
  | fgetLightSingleOwner | fgetLightNoFile | fgetLightMasked
  | fdgetPosHasFile | fposLockAtomicPos | fposLockShared | fposLockIterateShared
  | fdputFput | fdputPosUnlock | setCloexecFlag | dupFound | dupAllocOk
  -- fs/anon_inodes.c
  | anonGetfileOwner | anonMakeInode | anonInodeErr | anonGetfileFileErr
  -- fs/read_write.c
  | rwVerifyNegativeCount | rwVerifyHasPos | rwVerifyNegativePos | rwVerifyPosOverflow
  | newSyncReadQueued
  | vfsReadNotReadable | vfsReadCannotRead | vfsReadAccessFault | vfsReadVerifyError
  | vfsReadClamp | vfsReadHasRead | vfsReadHasReadIter | vfsReadPositive
  | filePposStream | ksysReadHasFile | ksysReadHasPpos | ksysReadRetNonneg | ksysReadStorePos
  | fileStartWriteNotRegular | fileEndWriteNotRegular
  | vfsWriteNotWritable | vfsWriteCannotWrite | vfsWriteAccessFault | vfsWriteVerifyError
  | vfsWriteClamp | vfsWriteHasWrite | vfsWriteHasWriteIter | vfsWritePositive
  | ksysWriteHasFile | ksysWriteHasPpos | ksysWriteRetNonneg | ksysWriteStorePos
  -- fs/fcntl.c
  | fcntlNoFile | fcntlPathFile | fcntlCaseGetfd | fcntlCaseSetfd | fcntlCaseGetfl | fcntlCaseSetfl | fcntlGetfdSet
  | setflAppendChanged | setflAppendOnly | setflNoatimeRequested | setflNoatimeNotSet | setflNotOwnerOrCapable
  | setflNotFifo | setflDirect | setflCannotOdirect | setflHasCheckFlags | setflError | setflFasyncChanged | setflHasFasync
  -- drivers/net/wireguard/allowedips.c
  | swapEndian32 | swapEndian128 | pushRcuNonNull | rootRemoveLenPositive | rootRemovePopped
  | rootRemoveHasPeer | fls128High | commonBits32 | commonBits128 | placementNode
  | placementCidrLe | placementPrefixMatches | placementExact | addCidrTooLong | addNoPeer
  | addEmptyTrie | addRootNoMem | addExact | addNewnodeNoMem | addNoParentNode
  | addNoDown | addNewnodeCoversDown | addNewnodeAtRoot | addIntermediateNoMem | addIntermediateAtRoot
  | freeHasRoot4 | freeHasRoot6 | removeListEmpty | removeListIter | removeHasBit0
  | removeHasBit1 | removeChildExists | removeLeafBit0 | removeLeafBit1 | removeParentIsNode
  | removeParentNoPeer | removeFreeParent | removeNotFreeParent | removeSiblingExists | readNodeHasCidr
  -- include/linux/refcount.h (add)
  | refcountAddNzZero | refcountAddNzRetry | refcountAddNzNegative | refcountAddNzWraps | refcountAddFromZero
  | refcountAddNegative | refcountAddWraps
  -- include/crypto/curve25519.h
  | genPublicNullSecret
  -- drivers/net/wireguard/cookie.c
  | cookieDeviceHasIdentity
  -- drivers/net/wireguard/noise.c
  | precomputeNoIdentity | precomputeNullPoint | handshakeInitHasPsk | keypairPutNull | expireNextKeypair
  | expireCurrentKeypair
  -- drivers/net/wireguard/peer.c
  | peerCreateMaxPeers | peerCreateNoMem | peerCreateDstCacheFail | peerGetMaybeZeroNull | peerGetMaybeZeroDead
  | peerRemoveNotDead | peerRemoveNull | peerRemoveAllIter1 | peerRemoveAllIter2 | peerPutNull
  | peerKrefPutReleased
  -- drivers/net/wireguard/peerlookup.c
  | pubkeyLookupMatch
  -- drivers/net/wireguard/socket.c
  | eqA4 | eqB4 | eqPort4 | eqAddr4 | eqSrc4
  | eqSrcIf4 | eqA6 | eqB6 | eqPort6 | eqAddr6
  | eqScope6 | eqSrc6 | eqANone | eqBNone | setEndpointEq
  | setEndpointV4 | setEndpointV6
  -- drivers/net/wireguard/netlink.c
  | lookupBothOrNeither | lookupHasIfindex | lookupHasIfname | lookupNoDev | lookupNoLinkOps
  | lookupNoKind | lookupKindMismatch | getAipNoNest | getAipPutCidr | getAipPutFamily
  | getAipFamily6 | getAipPutAddr | getPeerNoNest | getPeerPubkeyFail | getPeerFirst
  | getPeerPskFail | getPeerPutHandshake | getPeerPutKeepalive | getPeerPutTx | getPeerPutRx
  | getPeerPutProto | getPeerEp4 | getPeerEp6 | getPeerEpFail | getPeerNoAips
  | getPeerSeqUnset | getPeerSeqChanged | getPeerAipsNestFail | getPeerAipIter | getPeerAipFail
  | getStartErr | dumpNoHdr | dumpFirst | dumpPutPort | dumpPutFwmark
  | dumpPutIfindex | dumpPutIfname | dumpHasIdentity | dumpPutPrivate | dumpPutPublic
  | dumpNoPeersNest | dumpPeerListEmpty | dumpCursorSet | dumpCursorDead | dumpPeerIter
  | dumpGetPeerFail | dumpOutRetZero | dumpOutNotDone | dumpOutHasCursor | dumpRetErr
  | dumpDone | getDoneHasWg | setPortSame | setPortPeerIter | setPortNotRunning
  | aipNoFamily | aipNoAddr | aipNoCidr | aipV4Family | aipV4Cidr
  | aipV4Len | aipV6Family | aipV6Cidr | aipV6Len | peerHasPubkey
  | peerPubkeyLen | peerHasPsk | peerPskLen | peerHasFlags | peerBadFlags
  | peerHasProtocol | peerBadProtocol | peerNotFound | peerNewRemoveOrUpdate | peerSelfHasIdentity
  | peerSelfKeyMatch | peerCreateErr | peerRemoveMe | peerSetPsk | peerHasEndpoint
  | peerEndpointV4Len | peerEndpointV4Family | peerEndpointV6Len | peerEndpointV6Family | peerReplaceAips
  | peerHasAips | peerAipsIter | peerAipParseErr | peerAipErr | peerHasKeepalive
  | peerKeepaliveWasZero | peerKeepaliveNonzero | peerKeepaliveRunning | peerSendKeepalive | peerRunning
  | peerZeroPsk | setDevLookupErr | setDevHasFlags | setDevBadFlags | setDevHasPort
  | setDevHasFwmark | setDevNoNet | setDevNotCapable | setDevPermErr | setDevFwmark
  | setDevFwmarkPeerIter | setDevPort | setDevPortErr | setDevReplacePeers | setDevHasPrivateKey
  | setDevPrivateKeyLen | setDevKeyUnchanged | setDevGenPublic | setDevOldPeer | setDevSendStagedNoIdentity
  | setDevSendStagedRunning | setDevSendStagedKept | setDevSendStagedHasIdentity | setDevKeyPeerIter | setDevSendStagedPeer
  | setDevHasPeers | setDevPeersIter | setDevParseErr | setDevSetPeerErr | setDevZeroKey
  -- drivers/net/wireguard/allowedips.c
  | findNodeNode | findNodePrefixMatches | findNodeHasPeer | findNodeFullLength | lookupFound
  | lookupPeerGone | lookupDstV4 | lookupDstV6
  -- drivers/net/wireguard/queueing.h
  | checkProtoParsed | checkProtoMatches
  -- drivers/net/wireguard/device.c
  | openHasInet | openHasInet6 | openSocketError | openPeersIter | openKeepalive
  | xmitBadProtocol | xmitNoPeer | xmitNoPeerInet | xmitNoPeerInet6 | xmitEndpointNotInet
  | xmitEndpointNotInet6 | xmitValidDst | xmitNotGso | xmitWalk | xmitShareFailed
  | xmitStagedOverflow | xmitErrorInet | xmitErrorInet6
  -- drivers/net/wireguard/send.c
  | queuedNotRetry | queuedNotExpired | queuedDead | queuedAlreadyQueued | keepaliveStagedEmpty
  | keepaliveNoMem | stagedEmpty | stagedNoKeypair | stagedOrphanWalk
  -- drivers/net/wireguard/noise.c
  | keypairGetNull | keypairGetZero
  -- drivers/net/wireguard/socket.c
  | rxNoSock | rxNoWg
  -- drivers/net/wireguard/receive.c
  | hdrTooShort | hdrData | hdrDataLen | hdrInit | hdrInitLen
  | hdrResp | hdrRespLen | hdrCookie | hdrCookieLen | prepBadProtocol
  | prepTransportBelowHead | prepTransportBeyondTail | prepOffsetTooBig | prepOffsetBeyondLen | prepUdpLenSmall
  | prepUdpLenLying | prepPullFailed | prepTrimFailed | prepLenMismatch | prepNoHeaderLen
  | prepPullHeaderFailed | rxPrepareFailed | rxHandshake | rxData | rxRngNotReady
  | rxQueueBusy | rxProduceFailed | workerConsumed | hsCookie | hsUnderLoad
  | hsWasUnderLoad | hsLoadedOperand | hsLoadedCookieOk | hsNotLoaded | hsMacNoCookie
  | hsNeedsCookieLoaded | hsNeedsCookieMac | dataNoKeypair
  -- drivers/net/wireguard/cookie.c
  | macInvalid | macNoCookieCheck | cookieLookupMiss
  -- drivers/net/wireguard/peerlookup.c
  | idxMatch | idxFound
  -- drivers/net/wireguard/queueing.h
  | cpumaskWrap
  -- drivers/net/wireguard/noise.c
  | msgEphemeralCopy | kdfNoFirstDst | kdfNoFirstLen | kdfNoSecondDst | kdfNoSecondLen
  | kdfNoThirdDst | kdfNoThirdLen | mixDhNull | mixPrecomputedNull | msgDecryptFailed
  | consumeNoIdentity | consumeEsFailed | consumeStaticFailed | consumeNoPeer | consumeSsFailed
  | consumeTimestampFailed | consumeReplay | consumeFlood | consumeNewerTimestamp | consumeLaterTime
  | consumeFailedPut | respNotConsumed | respNoEphemeral | respEeFailed | respSeFailed
  | keypairCreateNoMem | sessionNotCreatedResponse | sessionNotConsumedResponse | sessionNoKeypair | sessionInitiator
  | sessionAlive | addKeypairInitiator
  -- drivers/net/wireguard/cookie.c
  | addMacCookieValid | addMacCookieFresh
  -- drivers/net/wireguard/send.c
  | respCreated | respSessionBegun
  -- drivers/net/wireguard/receive.c
  | hsSwitchInitiation | hsSwitchResponse | hsInitNeedsCookie | hsInitNoPeer | hsWrongPacket
  -- drivers/net/wireguard/socket.c
  | epFromSkbOk | epFromSkbInet | epFromSkbInet6
  -- drivers/net/wireguard/timers.c
  | timersDataSentNotPending | timersDataReceivedRunning | timersDataReceivedNotPending
  | modTimerRunning | modTimerAlive | traversalKeepalive | keypairPutUnreferenceNow | keypairKrefPutReleased
  | idxReplaceUnhashed | sendBufNoMem | sendSkbInet | sendSkbInet6 | sendSkbOk
  | initRateLimited | initCreated | initNoIdentity | initNoEphemeral | initEsFailed | initSsFailed
  | idxInsWalk1 | idxInsCollide1 | idxInsWalk2 | idxInsCollide2 | idxWalk | idxTypeMatch | idxPeerAlive
  -- D1 stream B
  -- drivers/net/wireguard/noise.c
  | crespNoIdentity | crespNoHandshake | crespNotCreatedInitiation | crespEeFailed | crespSeFailed
  | crespDecryptFailed | crespStateChanged | addKeypairHasNext
  -- drivers/net/wireguard/receive.c
  | hsRespNeedsCookie | hsRespNoPeer | hsRespSessionBegun
  -- D1 stream C: drivers/net/wireguard/send.c (staged packets with a keypair,
  -- create_data, encrypt_packet, the encrypt and tx workers, keep_key_fresh)
  | stagedKeyInvalid | stagedBirthdateExpired | stagedNonceIterate | stagedNonceRejected
  | createDataDead | createDataEpipe | createDataOk | createDataOkEpipe
  | padNoMtu | padOverMtu | encCowHeadFailed | encChecksumPartial | encChecksumHelpFailed
  | encCowDataFailed | encTooManyFrags | encSgvecFailed
  | encWorkerConsumed | encWorkerSkbIterate | encWorkerEncrypted | encWorkerNeedResched
  | txPacket | txNotUncrypted | txCrypted | txNeedResched
  | doneSkbIterate | doneSendOk | doneNotKeepalive | doneDataSent
  | freshKeypair | freshValid | freshCounter | freshInitiator | freshExpired | freshSend
  -- D1 stream C: drivers/net/wireguard/queueing.h
  | enqueuePeerQueueFull | enqueueRingFull | chooseCpuInvalid | chooseCpuOffline | chooseCpuIndexIterate
  | prevQueuePeeked
  -- D2 stream B: drivers/net/wireguard/receive.c (data messages: consume_data,
  -- the decrypt worker, counter_validate, the NAPI poll, consume_data_done,
  -- the receive side of keep_key_fresh)
  | dataPeerDead | dataEpipe | dataEnqueueOk | dataEnqueueOkEpipe
  | decNoKeypair | decKeyInvalid | decKeyExpired | decCounterLimit | decCowDataFailed | decTooManyFrags
  | decSgvecFailed | decDecryptFailed | decTrimFailed
  | decWorkerConsumed | decWorkerDecrypted | decWorkerNeedResched
  | ctrRejectCounter | ctrRejectTheirs | ctrTooOld | ctrAdvance | ctrClearIter
  | rxPollNoBudget | rxPollPacket | rxPollNotUncrypted | rxPollNotCrypted | rxPollCounterInvalid
  | rxPollEndpointFailed | rxPollFree | rxPollBudgetDone | rxPollComplete
  | doneReceivedNew | rxFreshSentLastminute | rxFreshKeypair | rxFreshValid | rxFreshInitiator
  | rxFreshExpired | rxFreshSend
  | doneRxKeepalive | doneNetworkBelowHead | doneMayPullV4 | doneVersion4 | doneVersion6 | doneMayPullV6
  | doneProtoIp | doneV4TooShort | doneProtoIpv6 | doneLenBeyond | doneTrimFailed | doneDishonestPeer
  -- D2 stream B: drivers/net/wireguard/noise.c, allowedips.c
  | receivedNotNew | receivedChanged | lookupSrcV4 | lookupSrcV6
  -- D2 stream B: INET_ECN_decapsulate inline in wg_packet_consume_data_done
  -- (include/net/inet_ecn.h)
  | ecnDecapInnerNotEct | ecnDecapOuterNotEct | ecnDecapRcZero | ecnDecapSetCe | ecnDecapOuterEct1
  -- D2 stream A: `ip_tunnel_ecn_encap` inline in wg_packet_send_staged_packets
  -- (include/linux/if_vlan.h, include/net/ip_tunnels.h, include/net/inet_ecn.h)
  | vlanTypeIsVlan | dsfieldIp | dsfieldIpv6 | ecnEncapInnerCe
  -- D2 stream A: calculate_skb_padding's `min(mtu, ALIGN(...))`
  | padClamped
  -- P stream 2 (begin): fs/pipe.c, include/linux/pipe_fs_i.h, fs/fcntl.c,
  -- fs/read_write.c (docs/2026-10-05-p-pipes.md section 11, Appendix A)
  | anonBufReleaseSole | anonBufReleaseNoTmp | pipeBufConfirmNoConfirm | pipeReadNull | pipeReadNotEmpty
  | pipeReadCharsOver | pipeReadWhole | pipeReadConfirmError | pipeReadShortCopy | pipeReadFaultNoRet
  | pipeReadPacket | pipeReadBufEmpty | pipeReadDone | pipeReadMore | pipeReadNoWriters | pipeReadHaveData
  | pipeReadNonblock | pipeReadNowait | pipeReadEmptyAtEnd | pipeReadWasFull | pipeReadWakeNextReader
  | pipeReadPositive | pipeWriteNull | pipeWriteNoReaders | pipeWriteChars | pipeWriteNotWasEmpty
  | pipeWriteCanMerge | pipeWriteFits | pipeWriteMergeConfirmErr | pipeWriteMergeShort | pipeWriteMergeDone
  | pipeWriteLoopNoReaders | pipeWriteLoopNoRet | pipeWriteNotFull | pipeWriteNoTmpPage
  | pipeWriteAllocFailed | pipeWriteAllocRet | pipeWritePacketized | pipeWriteShortCopy
  | pipeWriteShortCopyLeft | pipeWriteFaultNoRet | pipeWriteDone | pipeWriteStaleNotFull | pipeWriteNonblock
  | pipeWriteNowait | pipeWriteNoRet | pipeWriteFullAtOut | pipeWriteWasEmpty | pipeWritePollUsage
  | pipeWriteWakeNextWriter | pipeWritePositive | pipeWriteSbTrylock | pipeWriteUpdateTimeErr
  | putPipeInfoLast | putPipeInfoKill | pipeReleaseRead | pipeReleaseWrite | pipeReleaseOneSide
  | tooManySoftLimit | tooManySoftOver | tooManyHardLimit | tooManyHardOver | unprivNoResource
  | unprivNoAdmin | allocPipeInfoNoMem | allocPipeInfoOverMax | allocPipeInfoNotCapable | allocPipeInfoSoft
  | allocPipeInfoSoftUnpriv | allocPipeInfoHard | allocPipeInfoHardUnpriv | allocPipeInfoBufs
  | freePipeInfoLoop | freePipeInfoBufOps | freePipeInfoTmpPage | getPipeInodeNoInode | getPipeInodeNoPipe
  | createPipeFilesNoInode | createPipeFilesNotification | createPipeFilesWriterErr
  | createPipeFilesReaderErr | doPipeFlagsInvalid | doPipeFlagsCreateErr | doPipeFlagsFdrErr
  | doPipeFlagsFdwErr | doPipe2Ok | doPipe2CopyFault | roundPipeSizeTooBig | roundPipeSizeSmall
  | resizeRingNoMem | resizeRingBusy | resizeRingNonEmpty | resizeRingNoWrap | resizeRingHeadPart
  | resizeRingShrinkMaxUsage | pipeSetSizeZero | pipeSetSizeGrowMax | pipeSetSizeOverMax
  | pipeSetSizeNotCapable | pipeSetSizeGrowLimits | pipeSetSizeHard | pipeSetSizeSoft | pipeSetSizeUnpriv
  | pipeSetSizeResizeErr | getPipeInfoNotPipe | getPipeInfoNoPipe | pipeFcntlNoPipe | pipeFcntlSetSize
  | pipeFcntlGetSize | fcntlCasePipeSz | killFasyncList | newSyncWriteQueued | newSyncWritePositive
  | newSyncWritePpos | allocFileCloneOk
  -- P stream 2 (end)
  -- P stream 3 (begin): fs/inode.c, include/linux/time64.h, include/linux/fs.h,
  -- fs/libfs.c
  -- P stream 3 (end)
  -- P stream 2 signal (begin): kernel/signal.c
  | sendSigPriv | sendSigInfoInvalid | doSendSigLock | sendSignalLockedNoinfo | sendSignalLockedPriv
  | sendSignalNotPrepared | sendSignalShared | legacyQueueNotRt | legacyQueuePending | sendSignalLegacy
  | sendSignalSigkill | sendSignalKthread | sendSignalNotRt | sendSignalSiSpecial | sendSignalQueued
  | sendSignalNoinfo | sendSignalPrivInfo | sendSignalOverflowNotSpecial | sendSignalMultiprocess
  | prepareSignalGroupExit | prepareSignalStop | prepareSignalCont | sigIgnoredBlocked
  | sigIgnoredRealBlocked | sigIgnoredPtrace | completeSignalWants | wantsSignalBlocked
  | completeSignalPidType | sigqueueAllocNoUcounts | sigqueueAllocOverride | sigqueueAllocNull
  -- P stream 2 signal (end)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A recorded step: the decision, the outcome the mirror computed, and, for
    value comparisons, the two operands the C compares (as C values; negative
    numbers are two's complement in the check). -/
structure Step where
  decision : Decision
  outcome : Bool
  operands : Option (Int × Int) := none
  deriving Repr, BEq

/-- An inclusive range of source lines in one file. -/
structure Span where
  file : String
  lo : Nat
  hi : Nat
  deriving Repr, BEq

structure DecisionInfo where
  /-- `<C function>.<condition>` -/
  label : String
  file : String
  line : Nat
  whenTrue : List Span := []
  whenFalse : List Span := []

private def ev := "fs/eventfd.c"
private def ft := "fs/file_table.c"
private def fl := "fs/file.c"
private def op := "fs/open.c"
private def rw := "fs/read_write.c"
private def fc := "fs/fcntl.c"
private def an := "fs/anon_inodes.c"
private def fsh := "include/linux/fs.h"
private def fih := "include/linux/file.h"
private def inh := "fs/internal.h"
private def rch := "include/linux/refcount.h"
private def eph := "include/linux/eventpoll.h"
private def aip := "drivers/net/wireguard/allowedips.c"
private def wpe := "drivers/net/wireguard/peer.c"
private def wno := "drivers/net/wireguard/noise.c"
private def wnl := "drivers/net/wireguard/netlink.c"
private def wso := "drivers/net/wireguard/socket.c"
private def wpl := "drivers/net/wireguard/peerlookup.c"
private def wck := "drivers/net/wireguard/cookie.c"
private def c25 := "include/crypto/curve25519.h"
private def wrc := "drivers/net/wireguard/receive.c"
private def wtm := "drivers/net/wireguard/timers.c"
private def wdv := "drivers/net/wireguard/device.c"
private def wsd := "drivers/net/wireguard/send.c"
private def wqh := "drivers/net/wireguard/queueing.h"
private def vlh := "include/linux/if_vlan.h"
private def iph := "include/net/ip_tunnels.h"
private def ech := "include/net/inet_ecn.h"

private def sp (file : String) (lo hi : Nat) : Span := ⟨file, lo, hi⟩

private def d (label file : String) (line : Nat) (t f : List (Nat × Nat)) : DecisionInfo :=
  { label, file, line, whenTrue := t.map fun (a, b) => sp file a b,
    whenFalse := f.map fun (a, b) => sp file a b }

def Decision.info : Decision → DecisionInfo
  -- fs/eventfd.c
  | .eventfdFreeCtxHasId => d "eventfd_free_ctx.id_nonnegative" ev 84 [(85, 85)] []
  | .krefPutLast => d "eventfd_ctx_put.kref_put_released" ev 105 [(91, 93)] []
  -- __refcount_sub_and_test (refcount.h:262-278), inlined through kref_put;
  -- operands of one `&&`/`||` share their lines and bodies
  | .refcountSubPositive => d "__refcount_sub_and_test.old_positive" rch 269 [] []
  | .refcountSubToZero => d "__refcount_sub_and_test.old_equals_i" rch 269 [(270, 271)] []
  | .refcountSubNonpositive => d "__refcount_sub_and_test.old_nonpositive" rch 274 [] []
  | .refcountSubUnderflow => d "__refcount_sub_and_test.underflow" rch 274 [] []
  | .ctxDoReadSemaphore => d "eventfd_ctx_do_read.semaphore" ev 180 [] []
  | .ctxDoReadCountNonzero => d "eventfd_ctx_do_read.count_nonzero" ev 180 [] []
  | .eventfdReadShort => d "eventfd_read.short_buffer" ev 220 [(221, 221)] [(222, 242)]
  | .eventfdReadEmpty => d "eventfd_read.empty" ev 223 [(224, 233)] [(235, 235)]
  | .eventfdReadNonblock => d "eventfd_read.o_nonblock" ev 224 [] [(225, 225)]
  -- 226-227 are shared with the O_NONBLOCK operand
  | .eventfdReadNowait => d "eventfd_read.iocb_nowait" ev 225 [] [(230, 233)]
  | .eventfdReadWaitqueueActive => d "eventfd_read.waitqueue_active" ev 237 [(238, 238)] []
  | .eventfdReadCopyFault => d "eventfd_read.copy_to_iter_short" ev 241 [(242, 242)] []
  | .eventfdWriteWrongSize => d "eventfd_write.wrong_size" ev 254 [(255, 255)] [(256, 277)]
  | .eventfdWriteCopyFault => d "eventfd_write.copy_from_user_fault" ev 256 [(257, 257)] [(258, 277)]
  | .eventfdWriteReserved => d "eventfd_write.ullong_max" ev 258 [(259, 259)] [(260, 277)]
  | .eventfdWriteFits => d "eventfd_write.fits" ev 262 [(263, 263)] [(264, 269)]
  | .eventfdWriteBlocking => d "eventfd_write.blocking" ev 264 [(265, 268)] []
  | .eventfdWriteResPositive => d "eventfd_write.res_positive" ev 270 [(271, 275)] []
  | .eventfdWriteWaitqueueActive => d "eventfd_write.waitqueue_active" ev 273 [(274, 274)] []
  -- 418 `return fd` is the epilogue shared with every early return
  | .doEventfdInvalidFlags => d "do_eventfd.invalid_flags" ev 390 [(391, 391)] [(393, 417)]
  | .doEventfdNoMem => d "do_eventfd.kmalloc_failed" ev 394 [(395, 395)] [(397, 417)]
  | .doEventfdFdError => d "do_eventfd.fd_error" ev 406 [(407, 407)] [(409, 417)]
  | .doEventfdFileError => d "do_eventfd.file_error" ev 410 [(411, 413)] [(416, 417)]
  -- fs/file_table.c and headers
  | .fileFreeAccounted => d "file_free.accounted" ft 90 [(91, 91)] []
  | .fileFreeBacking => d "file_free.backing" ft 93 [(94, 94)] [(96, 96)]
  | .allocEmptyFileOverMax => d "alloc_empty_file.nr_files_at_max" ft 223 [] []
  | .allocEmptyFileNotCapable => d "alloc_empty_file.not_capable" ft 223 [(228, 229)] []
  | .allocEmptyFileNoMem => d "alloc_empty_file.zalloc_failed" ft 233 [(234, 234)] [(236, 244)]
  | .iocbFlagsAppend => d "iocb_flags.o_append" fsh 3593 [(3594, 3594)] []
  | .iocbFlagsDirect => d "iocb_flags.o_direct" fsh 3595 [(3596, 3596)] []
  | .iocbFlagsDsync => d "iocb_flags.o_dsync" fsh 3597 [(3598, 3598)] []
  | .iocbFlagsSync => d "iocb_flags.o_sync" fsh 3599 [(3600, 3600)] []
  | .fileInitPathLlseek => d "file_init_path.llseek" ft 338 [(339, 339)] []
  | .fileInitPathModeRead => d "file_init_path.fmode_read" ft 340 [(341, 341)] []
  | .fileInitPathHasRead => d "file_init_path.fop_read" ft 341 [] []
  -- 342 and 345 are shared with the preceding `fop->read`/`fop->write` operand
  | .fileInitPathHasReadIter => d "file_init_path.fop_read_iter" ft 341 [] []
  | .fileInitPathModeWrite => d "file_init_path.fmode_write" ft 343 [(344, 344)] []
  | .fileInitPathHasWrite => d "file_init_path.fop_write" ft 344 [] []
  | .fileInitPathHasWriteIter => d "file_init_path.fop_write_iter" ft 344 [] []
  | .fileInitPathReadOnly => d "file_init_path.read_only" ft 349 [(350, 350)] []
  | .allocFileOk => d "alloc_file.ok" ft 366 [(367, 367)] []
  | .allocPathPseudoFail => d "alloc_path_pseudo.d_alloc_failed" ft 375 [(376, 376)] [(377, 378)]
  | .allocFilePseudoErr => d "alloc_file_pseudo.file_error" ft 395 [(396, 397)] []
  | .putFileAccessReadOnly => d "put_file_access.read_only" inh 116 [(117, 117)] []
  | .putFileAccessWriter => d "put_file_access.fmode_writer" inh 118 [(119, 119)] []
  | .fputFinalNotOpened => d "__fput.not_opened" ft 449 [(450, 450)] [(452, 479)]
  -- the f_op load attributed to 464 is shared with the release test at 467
  | .eventpollReleaseLinked => d "eventpoll_release.linked" eph 45 [(53, 53)] [(46, 46)]
  | .fputFinalFasync => d "__fput.fasync" ft 463 [(465, 465)] []
  | .fputFinalRelease => d "__fput.fop_release" ft 467 [(468, 468)] []
  | .fputFinalCharDevice => d "__fput.char_device" ft 469 [] []
  | .fputFinalHasCdev => d "__fput.has_cdev" ft 469 [] []
  | .fputFinalNotPath => d "__fput.not_fmode_path" ft 470 [(471, 471)] []
  | .fileOwnerRelease => d "file_f_owner_release.has_owner" fc 121 [(122, 123)] []
  | .fputFinalNeedUnmount => d "__fput.need_unmount" ft 477 [(478, 478)] []
  | .fputLast => d "fput.last_reference" ft 519 [(520, 538)] []
  | .fputNotOpened => d "fput.not_opened" ft 522 [(523, 524)] [(526, 538)]
  | .fputInInterrupt => d "fput.in_interrupt" ft 526 [] []
  | .fputKthread => d "fput.pf_kthread" ft 526 [] [(527, 527)]
  | .fputTaskWorkAddFailed => d "fput.task_work_add_failed" ft 528 [] [(529, 529)]
  | .fputSyncLast => d "__fput_sync.last_reference" ft 552 [(553, 553)] []
  -- fs/open.c
  | .filpFlushCountZero => d "filp_flush.file_count_zero" op 1526 [(1529, 1529)] [(1532, 1539)]
  | .filpFlushHasFlush => d "filp_flush.fop_flush" op 1532 [(1533, 1533)] []
  | .filpFlushNotPath => d "filp_flush.not_fmode_path" op 1535 [(1536, 1537)] []
  | .closeNoFile => d "__do_sys_close.no_file" op 1564 [(1565, 1565)] [(1567, 1582)]
  | .closeRestartSys => d "__do_sys_close.erestartsys" op 1576 [] []
  | .closeRestartNoIntr => d "__do_sys_close.erestartnointr" op 1577 [] []
  | .closeRestartNoHand => d "__do_sys_close.erestartnohand" op 1578 [] []
  | .closeRestartBlock => d "__do_sys_close.erestart_restartblock" op 1579 [(1580, 1580)] []
  -- fs/file.c
  | .clearCloexecWasSet => d "__clear_close_on_exec.was_set" fl 263 [(264, 264)] []
  -- do_dup2's inlined copy reaches the point attributed to 272 on the not-full path
  | .setOpenFdFullWord => d "__set_open_fd.word_full" fl 271 [] []
  | .findNextFdAllFull => d "find_next_fd.all_words_full" fl 482 [(483, 483)] [(484, 486)]
  | .findNextFdSkipFullWords => d "find_next_fd.skip_full_words" fl 484 [(485, 485)] []
  -- 253 `return expanded` is the epilogue shared with the early return at 233
  | .expandFilesFits => d "expand_files.fits" fl 232 [(233, 233)] [(236, 252)]
  | .expandFilesOverNrOpen => d "expand_files.over_nr_open" fl 236 [(237, 237)] [(239, 252)]
  | .expandFilesResizeInProgress => d "expand_files.resize_in_progress" fl 239 [(240, 244)] [(248, 252)]
  | .allocFdtableOverNrOpen => d "alloc_fdtable.over_nr_open" fl 126 [(127, 129)] []
  | .allocFdtableBelowWanted => d "alloc_fdtable.below_wanted" fl 128 [(129, 129)] []
  | .allocFdtableOverIntMax => d "alloc_fdtable.over_int_max" fl 144 [(145, 145)] [(147, 167)]
  | .allocFdtableNoMem => d "alloc_fdtable.kmalloc_failed" fl 148 [(149, 149)] [(150, 167)]
  | .allocFdtableFdArrayNoMem => d "alloc_fdtable.fd_array_failed" fl 152 [(153, 153)] [(154, 167)]
  | .allocFdtableBitmapNoMem => d "alloc_fdtable.bitmaps_failed" fl 159 [(160, 160)] [(161, 167)]
  | .copyFdtableShrink => d "copy_fdtable.shrink" fl 77 [] [(79, 84)]
  | .expandFdtableShared => d "expand_fdtable.files_shared" fl 196 [(197, 197)] []
  | .expandFdtableAllocError => d "expand_fdtable.alloc_error" fl 200 [(201, 201)] [(202, 210)]
  | .expandFdtableBugNr => d "expand_fdtable.nr_below_max_fds" fl 203 [] [(204, 210)]
  | .expandFdtableFreeOld => d "expand_fdtable.free_old" fl 206 [(207, 207)] []
  | .allocFdBelowNextFd => d "alloc_fd.start_below_next_fd" fl 503 [(504, 504)] []
  | .allocFdSearch => d "alloc_fd.search_bitmap" fl 506 [(507, 507)] []
  | .allocFdLimit => d "alloc_fd.at_limit" fl 514 [(515, 515)] [(517, 543)]
  | .allocFdExpandError => d "alloc_fd.expand_error" fl 518 [(519, 519)] [(525, 543)]
  | .allocFdExpanded => d "alloc_fd.expanded" fl 525 [(526, 526)] [(528, 543)]
  | .allocFdUpdateNextFd => d "alloc_fd.update_next_fd" fl 528 [(529, 529)] []
  | .allocFdCloexec => d "alloc_fd.o_cloexec" fl 532 [(533, 533)] [(535, 535)]
  | .allocFdSlotNotNull => d "alloc_fd.slot_not_null" fl 539 [(540, 541)] []
  | .putUnusedFdLowerNextFd => d "__put_unused_fd.lower_next_fd" fl 565 [(566, 566)] []
  | .fdInstallBacking => d "fd_install.fmode_backing" fl 600 [(601, 601)] [(603, 619)]
  | .fdInstallResizeInProgress => d "fd_install.resize_in_progress" fl 605 [(606, 612)] [(615, 619)]
  | .fdInstallSlotBusy => d "fd_install.slot_busy" fl 617 [] [(618, 618)]
  -- 643 `return NULL` shares its block with the final return
  | .closeFdOutOfRange => d "file_close_fd_locked.out_of_range" fl 642 [] [(645, 651)]
  | .closeFdFound => d "file_close_fd_locked.found" fl 647 [(648, 649)] []
  | .getFileFromZero => d "get_file.prior_zero" fsh 1125 [] []
  | .doDup2NoTofree => d "do_dup2.no_tofree" fl 1229 [] []
  | .doDup2FdOpen => d "do_dup2.fd_is_open" fl 1229 [(1230, 1230), (1246, 1247)] []
  | .doDup2Cloexec => d "do_dup2.o_cloexec" fl 1234 [(1235, 1235)] [(1237, 1237)]
  | .doDup2Replace => d "do_dup2.replace" fl 1240 [(1241, 1241)] []
  -- 1356 `return do_dup2(...)` shares its block with the early-return epilogue
  | .dup3InvalidFlags => d "ksys_dup3.invalid_flags" fl 1337 [(1338, 1338)] [(1340, 1355)]
  | .dup3Equal => d "ksys_dup3.equal_fds" fl 1340 [(1341, 1341)] [(1343, 1355)]
  | .dup3TargetLimit => d "ksys_dup3.newfd_at_rlimit" fl 1343 [(1344, 1344)] [(1346, 1355)]
  | .dup3NoFile => d "ksys_dup3.no_file" fl 1349 [(1350, 1350)] [(1351, 1355)]
  | .dup3ExpandError => d "ksys_dup3.expand_error" fl 1351 [(1352, 1354)] []
  | .dup3ExpandEmfile => d "ksys_dup3.expand_emfile" fl 1352 [(1353, 1353)] []
  | .fgetRcuNoFile => d "__fget_files_rcu.no_file" fl 952 [(953, 953)] [(966, 1002)]
  | .fgetRcuIncNotZeroFailed => d "__fget_files_rcu.inc_not_zero_failed" fl 966 [(967, 967)] [(983, 1002)]
  -- the two stale-entry operands share their body; fget_raw passes mask 0, so the
  -- compiler removes the test at 993 that would otherwise follow both being false
  | .fgetRcuEntryChanged => d "__fget_files_rcu.entry_changed" fl 983 [] []
  | .fgetRcuTableChanged => d "__fget_files_rcu.table_changed" fl 984 [] []
  | .fgetRcuMasked => d "__fget_files_rcu.masked" fl 993 [(994, 995)] [(1002, 1002)]
  | .fgetLightSingleOwner => d "__fget_light.single_owner" fl 1121 [(1122, 1125)] [(1127, 1130)]
  | .fgetLightNoFile => d "__fget_light.no_file" fl 1123 [] []
  | .fgetLightMasked => d "__fget_light.masked" fl 1123 [] [(1125, 1125)]
  -- 1157 runs only when FMODE_ATOMIC_POS is also set; 1156 has no KCOV point
  | .fdgetPosHasFile => d "fdget_pos.has_file" fl 1165 [] []
  | .fposLockAtomicPos => d "file_needs_f_pos_lock.fmode_atomic_pos" fl 1156 [(1157, 1157)] []
  | .fposLockShared => d "file_needs_f_pos_lock.count_above_one" fl 1157 [] []
  -- 1166-1167 are shared with the count operand
  | .fposLockIterateShared => d "file_needs_f_pos_lock.iterate_shared" fl 1157 [] []
  | .fdputFput => d "fdput.fdput_fput" fih 62 [(63, 63)] []
  | .fdputPosUnlock => d "fdput_pos.pos_unlock" fih 77 [(78, 78)] []
  | .setCloexecFlag => d "set_close_on_exec.flag" fl 1189 [(1190, 1190)] [(1192, 1192)]
  | .dupFound => d "__do_sys_dup.found" fl 1394 [(1395, 1399)] []
  | .dupAllocOk => d "__do_sys_dup.fd_allocated" fl 1396 [(1397, 1397)] [(1399, 1399)]
  -- fs/anon_inodes.c
  | .anonGetfileOwner => d "__anon_inode_getfile.module_owner" an 99 [(100, 100)] []
  | .anonMakeInode => d "__anon_inode_getfile.make_inode" an 102 [(103, 108)] [(110, 119)]
  | .anonInodeErr => d "__anon_inode_getfile.inode_error" an 111 [(112, 113)] []
  | .anonGetfileFileErr => d "__anon_inode_getfile.file_error" an 124 [(125, 125), (133, 136)] [(127, 131)]
  -- fs/read_write.c
  | .rwVerifyNegativeCount => d "rw_verify_area.negative_count" rw 453 [(454, 454)] [(456, 474)]
  | .rwVerifyHasPos => d "rw_verify_area.has_ppos" rw 456 [(457, 467)] []
  -- the unsigned_offsets load at 460 is hoisted onto the pos >= 0 path
  | .rwVerifyNegativePos => d "rw_verify_area.negative_pos" rw 459 [(461, 463)] [(464, 466)]
  | .rwVerifyPosOverflow => d "rw_verify_area.pos_overflow" rw 464 [(465, 466)] []
  | .newSyncReadQueued => d "new_sync_read.eiocbqueued" rw 489 [] []
  | .vfsReadNotReadable => d "vfs_read.not_fmode_read" rw 553 [(554, 554)] [(555, 577)]
  | .vfsReadCannotRead => d "vfs_read.not_fmode_can_read" rw 555 [(556, 556)] [(557, 577)]
  | .vfsReadAccessFault => d "vfs_read.access_not_ok" rw 557 [(558, 558)] [(560, 577)]
  | .vfsReadVerifyError => d "vfs_read.verify_error" rw 561 [(562, 562)] [(563, 577)]
  -- the block attributed to 567 is shared with the read_iter call
  | .vfsReadClamp => d "vfs_read.clamp_count" rw 563 [(564, 564)] []
  | .vfsReadHasRead => d "vfs_read.fop_read" rw 566 [] [(568, 571)]
  | .vfsReadHasReadIter => d "vfs_read.fop_read_iter" rw 568 [(569, 569)] [(571, 571)]
  | .vfsReadPositive => d "vfs_read.ret_positive" rw 572 [(573, 574)] []
  | .filePposStream => d "file_ppos.fmode_stream" rw 698 [] []
  | .ksysReadHasFile => d "ksys_read.has_file" rw 706 [(707, 715)] []
  | .ksysReadHasPpos => d "ksys_read.has_ppos" rw 708 [(709, 710)] []
  | .ksysReadRetNonneg => d "ksys_read.ret_nonnegative" rw 713 [] []
  | .ksysReadStorePos => d "ksys_read.store_pos" rw 713 [(714, 714)] []
  | .fileStartWriteNotRegular => d "file_start_write.not_regular" fsh 2998 [(2999, 2999)] [(3000, 3000)]
  | .fileEndWriteNotRegular => d "file_end_write.not_regular" fsh 3018 [(3019, 3019)] [(3020, 3020)]
  | .vfsWriteNotWritable => d "vfs_write.not_fmode_write" rw 667 [(668, 668)] [(669, 692)]
  | .vfsWriteCannotWrite => d "vfs_write.not_fmode_can_write" rw 669 [(670, 670)] [(671, 692)]
  | .vfsWriteAccessFault => d "vfs_write.access_not_ok" rw 671 [(672, 672)] [(674, 692)]
  | .vfsWriteVerifyError => d "vfs_write.verify_error" rw 675 [(676, 676)] [(677, 692)]
  | .vfsWriteClamp => d "vfs_write.clamp_count" rw 677 [(678, 678)] []
  | .vfsWriteHasWrite => d "vfs_write.fop_write" rw 680 [(681, 681)] [(682, 685)]
  | .vfsWriteHasWriteIter => d "vfs_write.fop_write_iter" rw 682 [(683, 683)] [(685, 685)]
  | .vfsWritePositive => d "vfs_write.ret_positive" rw 686 [(687, 688)] []
  | .ksysWriteHasFile => d "ksys_write.has_file" rw 730 [(731, 739)] []
  | .ksysWriteHasPpos => d "ksys_write.has_ppos" rw 732 [(733, 734)] []
  | .ksysWriteRetNonneg => d "ksys_write.ret_nonnegative" rw 737 [] []
  | .ksysWriteStorePos => d "ksys_write.store_pos" rw 737 [(738, 738)] []
  -- fs/fcntl.c
  | .fcntlNoFile => d "__do_sys_fcntl.no_file" fc 578 [(579, 579)] [(581, 591)]
  | .fcntlPathFile => d "__do_sys_fcntl.fmode_path" fc 581 [(582, 583)] []
  | .fcntlCaseGetfd => d "do_fcntl.case_f_getfd" fc 464 [(465, 466)] []
  | .fcntlCaseSetfd => d "do_fcntl.case_f_setfd" fc 467 [(468, 470)] []
  | .fcntlCaseGetfl => d "do_fcntl.case_f_getfl" fc 471 [(472, 473)] []
  | .fcntlGetfdSet => d "do_fcntl.close_on_exec_set" fc 465 [] []
  | .fcntlCaseSetfl => d "do_fcntl.case_f_setfl" fc 474 [(475, 476)] []
  -- setfl (fcntl.c:39-89); operands of one `&&` share their lines and bodies
  | .setflAppendChanged => d "setfl.o_append_changed" fc 48 [] []
  | .setflAppendOnly => d "setfl.is_append" fc 48 [(49, 49)] []
  | .setflNoatimeRequested => d "setfl.o_noatime_requested" fc 52 [] []
  | .setflNoatimeNotSet => d "setfl.o_noatime_not_set" fc 52 [(53, 54)] []
  | .setflNotOwnerOrCapable => d "setfl.not_owner_or_capable" fc 53 [(54, 54)] []
  | .setflNotFifo => d "setfl.not_fifo" fc 62 [] []
  | .setflDirect => d "setfl.o_direct" fc 63 [] []
  | .setflCannotOdirect => d "setfl.not_fmode_can_odirect" fc 64 [(65, 65)] []
  | .setflHasCheckFlags => d "setfl.fop_check_flags" fc 67 [(68, 68)] []
  | .setflError => d "setfl.error" fc 69 [(70, 70)] []
  | .setflFasyncChanged => d "setfl.fasync_changed" fc 75 [] []
  | .setflHasFasync => d "setfl.fop_fasync" fc 75 [(76, 80)] []
  -- drivers/net/wireguard/allowedips.c
  | .swapEndian32 => d "swap_endian.bits_32" aip 15 [(16, 16)] [(17, 20)]
  | .swapEndian128 => d "swap_endian.bits_128" aip 17 [(18, 19)] []
  | .pushRcuNonNull => d "push_rcu.non_null" aip 44 [(45, 47)] []
  | .rootRemoveLenPositive => d "root_remove_peer_lists.len_positive" aip 74 [] []
  | .rootRemovePopped => d "root_remove_peer_lists.popped_non_null" aip 74 [(75, 78)] []
  | .rootRemoveHasPeer => d "root_remove_peer_lists.has_peer" aip 77 [(78, 78)] []
  | .fls128High => d "fls128.high_nonzero" aip 84 [] []
  | .commonBits32 => d "common_bits.bits_32" aip 90 [(91, 91)] [(92, 95)]
  | .commonBits128 => d "common_bits.bits_128" aip 92 [(93, 95)] [(96, 96)]
  | .placementNode => d "node_placement.node" aip 157 [] []
  | .placementCidrLe => d "node_placement.cidr_le" aip 157 [] []
  | .placementPrefixMatches => d "node_placement.prefix_matches" aip 157 [(158, 163)] []
  | .placementExact => d "node_placement.exact" aip 159 [(160, 161)] [(163, 163)]
  | .addCidrTooLong => d "add.cidr_too_long" aip 186 [] []
  -- 187's point is the epilogue every `return 0` also runs
  | .addNoPeer => d "add.no_peer" aip 186 [] [(189, 189)]
  | .addEmptyTrie => d "add.empty_trie" aip 189 [(190, 197)] [(199, 199)]
  | .addRootNoMem => d "add.root_no_mem" aip 191 [(192, 192)] [(193, 197)]
  | .addExact => d "add.exact" aip 199 [(200, 202)] [(205, 210)]
  | .addNewnodeNoMem => d "add.newnode_no_mem" aip 206 [(207, 207)] [(208, 210)]
  | .addNoParentNode => d "add.no_parent_node" aip 212 [(213, 213)] [(215, 221)]
  | .addNoDown => d "add.no_down" aip 217 [(218, 219)] []
  | .addNewnodeCoversDown => d "add.newnode_covers_down" aip 225 [(226, 231)] [(234, 249)]
  | .addNewnodeAtRoot => d "add.newnode_at_root" aip 227 [(228, 228)] [(230, 230)]
  | .addIntermediateNoMem => d "add.intermediate_no_mem" aip 235 [(236, 238)] [(240, 249)]
  | .addIntermediateAtRoot => d "add.intermediate_at_root" aip 245 [(246, 246)] [(248, 248)]
  | .freeHasRoot4 => d "wg_allowedips_free.has_root4" aip 265 [(266, 270)] []
  | .freeHasRoot6 => d "wg_allowedips_free.has_root6" aip 272 [(273, 277)] []
  | .removeListEmpty => d "wg_allowedips_remove_by_peer.list_empty" aip 309 [(310, 310)] [(311, 313)]
  | .removeListIter => d "wg_allowedips_remove_by_peer.iterate" aip 312 [(313, 314)] []
  | .removeHasBit0 => d "wg_allowedips_remove_by_peer.has_bit0" aip 315 [] []
  | .removeHasBit1 => d "wg_allowedips_remove_by_peer.has_bit1" aip 315 [(316, 316)] []
  | .removeChildExists => d "wg_allowedips_remove_by_peer.child" aip 319 [(320, 320)] []
  | .removeLeafBit0 => d "wg_allowedips_remove_by_peer.no_bit0" aip 325 [(326, 326)] []
  | .removeLeafBit1 => d "wg_allowedips_remove_by_peer.no_bit1" aip 326 [(327, 327)] []
  | .removeParentIsNode => d "wg_allowedips_remove_by_peer.parent_is_node" aip 327 [(328, 328)] []
  | .removeParentNoPeer => d "wg_allowedips_remove_by_peer.parent_no_peer" aip 328 [] []
  | .removeFreeParent => d "wg_allowedips_remove_by_peer.free_parent" aip 329 [(330, 332)] []
  | .removeNotFreeParent => d "wg_allowedips_remove_by_peer.not_free_parent" aip 334 [(335, 335)] [(336, 339)]
  | .removeSiblingExists => d "wg_allowedips_remove_by_peer.sibling" aip 336 [(337, 337)] []
  | .readNodeHasCidr => d "wg_allowedips_read_node.has_cidr" aip 348 [(349, 349)] []
  -- include/linux/refcount.h (add)
  | .refcountAddNzZero => d "__refcount_add_not_zero.old_zero" rch 145 [(146, 146)] [(147, 147)]
  | .refcountAddNzRetry => d "__refcount_add_not_zero.cmpxchg_failed" rch 147 [] []
  | .refcountAddNzNegative => d "__refcount_add_not_zero.old_negative" rch 152 [] []
  | .refcountAddNzWraps => d "__refcount_add_not_zero.wraps" rch 152 [] []
  | .refcountAddFromZero => d "__refcount_add.old_zero" rch 189 [(190, 190)] [(191, 191)]
  | .refcountAddNegative => d "__refcount_add.old_negative" rch 191 [] []
  | .refcountAddWraps => d "__refcount_add.wraps" rch 191 [] []
  -- include/crypto/curve25519.h
  | .genPublicNullSecret => d "curve25519_generate_public.null_secret" c25 50 [(52, 52)] [(54, 58)]
  -- drivers/net/wireguard/cookie.c
  | .cookieDeviceHasIdentity => d "wg_cookie_checker_precompute_device_keys.has_identity" wck 47 [(48, 53)] [(55, 57)]
  -- drivers/net/wireguard/noise.c
  | .precomputeNoIdentity => d "wg_noise_precompute_static_static.no_identity" wno 50 [] [(51, 53)]
  | .precomputeNullPoint => d "wg_noise_precompute_static_static.null_point" wno 51 [] []
  | .handshakeInitHasPsk => d "wg_noise_handshake_init.has_preshared_key" wno 70 [(71, 72)] []
  | .keypairPutNull => d "wg_noise_keypair_put.null" wno 133 [(134, 134)] [(135, 139)]
  | .expireNextKeypair => d "wg_noise_expire_current_peer_keypairs.next_keypair" wno 189 [(190, 190)] []
  | .expireCurrentKeypair => d "wg_noise_expire_current_peer_keypairs.current_keypair" wno 193 [(194, 194)] []
  -- drivers/net/wireguard/peer.c
  -- 31's point is the epilogue the successful return also runs
  | .peerCreateMaxPeers => d "wg_peer_create.max_peers" wpe 30 [] [(33, 33)]
  | .peerCreateNoMem => d "wg_peer_create.no_mem" wpe 34 [(35, 35)] [(36, 36)]
  | .peerCreateDstCacheFail => d "wg_peer_create.dst_cache_failed" wpe 36 [(37, 37), (66, 68)] [(39, 64)]
  | .peerGetMaybeZeroNull => d "wg_peer_get_maybe_zero.null" wpe 75 [] []
  | .peerGetMaybeZeroDead => d "wg_peer_get_maybe_zero.refcount_zero" wpe 75 [] [(77, 77)]
  | .peerRemoveNotDead => d "peer_remove_after_dead.not_dead" wpe 96 [] []
  | .peerRemoveNull => d "wg_peer_remove.null" wpe 158 [(159, 159)] [(160, 164)]
  | .peerRemoveAllIter1 => d "wg_peer_remove_all.make_dead_iterate" wpe 177 [(178, 179)] []
  | .peerRemoveAllIter2 => d "wg_peer_remove_all.remove_iterate" wpe 182 [(183, 183)] []
  | .peerPutNull => d "wg_peer_put.null" wpe 225 [(226, 226)] [(227, 227)]
  | .peerKrefPutReleased => d "wg_peer_put.kref_put_released" wpe 227 [(202, 220)] []
  -- drivers/net/wireguard/peerlookup.c
  | .pubkeyLookupMatch => d "wg_pubkey_hashtable_lookup.match" wpl 62 [(64, 65)] []
  -- drivers/net/wireguard/socket.c
  | .eqA4 => d "endpoint_eq.a_inet" wso 260 [] []
  | .eqB4 => d "endpoint_eq.b_inet" wso 260 [] []
  | .eqPort4 => d "endpoint_eq.port4" wso 261 [] []
  | .eqAddr4 => d "endpoint_eq.addr4" wso 262 [] []
  | .eqSrc4 => d "endpoint_eq.src4" wso 263 [] []
  | .eqSrcIf4 => d "endpoint_eq.src_if4" wso 263 [] []
  | .eqA6 => d "endpoint_eq.a_inet6" wso 264 [] []
  | .eqB6 => d "endpoint_eq.b_inet6" wso 265 [] []
  | .eqPort6 => d "endpoint_eq.port6" wso 266 [] []
  | .eqAddr6 => d "endpoint_eq.addr6" wso 267 [] []
  | .eqScope6 => d "endpoint_eq.scope6" wso 268 [] []
  | .eqSrc6 => d "endpoint_eq.src6" wso 269 [] []
  | .eqANone => d "endpoint_eq.a_unset" wso 270 [] []
  | .eqBNone => d "endpoint_eq.b_unset" wso 270 [] []
  | .setEndpointEq => d "wg_socket_set_peer_endpoint.equal" wso 281 [(282, 282)] [(283, 284)]
  | .setEndpointV4 => d "wg_socket_set_peer_endpoint.inet" wso 284 [(285, 287)] [(288, 288)]
  | .setEndpointV6 => d "wg_socket_set_peer_endpoint.inet6" wso 288 [(289, 290)] [(292, 292)]
  -- drivers/net/wireguard/netlink.c
  | .lookupBothOrNeither => d "lookup_interface.both_or_neither" wnl 57 [(58, 58)] [(59, 59)]
  | .lookupHasIfindex => d "lookup_interface.has_ifindex" wnl 59 [(60, 61)] [(62, 62)]
  | .lookupHasIfname => d "lookup_interface.has_ifname" wnl 62 [(63, 64)] []
  | .lookupNoDev => d "lookup_interface.no_dev" wnl 65 [(66, 66)] [(67, 67)]
  | .lookupNoLinkOps => d "lookup_interface.no_link_ops" wnl 67 [] []
  | .lookupNoKind => d "lookup_interface.no_kind" wnl 67 [] []
  | .lookupKindMismatch => d "lookup_interface.kind_mismatch" wnl 68 [(69, 70)] [(72, 72)]
  | .getAipNoNest => d "get_allowedips.no_nest" wnl 81 [(82, 82)] [(84, 84)]
  | .getAipPutCidr => d "get_allowedips.put_cidr_failed" wnl 84 [] [(85, 85)]
  | .getAipPutFamily => d "get_allowedips.put_family_failed" wnl 85 [] [(86, 86)]
  | .getAipFamily6 => d "get_allowedips.inet6_length" wnl 86 [] []
  | .getAipPutAddr => d "get_allowedips.put_addr_failed" wnl 86 [] [(92, 93)]
  | .getPeerNoNest => d "get_peer.no_nest" wnl 113 [(114, 114)] [(116, 118)]
  | .getPeerPubkeyFail => d "get_peer.put_public_key_failed" wnl 120 [(121, 121)] [(123, 123)]
  | .getPeerFirst => d "get_peer.first_part" wnl 123 [(124, 162)] []
  -- the point DWARF gives line 135 starts the `goto no_allowedips` block of line 164
  | .getPeerPskFail => d "get_peer.put_preshared_key_failed" wnl 134 [] [(137, 138)]
  | .getPeerPutHandshake => d "get_peer.put_last_handshake_failed" wnl 137 [] [(139, 140)]
  | .getPeerPutKeepalive => d "get_peer.put_keepalive_failed" wnl 139 [] [(141, 142)]
  | .getPeerPutTx => d "get_peer.put_tx_bytes_failed" wnl 141 [] [(143, 144)]
  | .getPeerPutRx => d "get_peer.put_rx_bytes_failed" wnl 143 [] [(145, 145)]
  | .getPeerPutProto => d "get_peer.put_protocol_version_failed" wnl 145 [] [(148, 149)]
  | .getPeerEp4 => d "get_peer.endpoint_inet" wnl 149 [(150, 152)] [(153, 153)]
  | .getPeerEp6 => d "get_peer.endpoint_inet6" wnl 153 [(154, 156)] []
  | .getPeerEpFail => d "get_peer.put_endpoint_failed" wnl 158 [(159, 159)] [(160, 162)]
  | .getPeerNoAips => d "get_peer.no_allowedips" wnl 164 [(165, 165)] [(166, 166)]
  | .getPeerSeqUnset => d "get_peer.seq_unset" wnl 166 [(167, 167)] [(168, 168)]
  | .getPeerSeqChanged => d "get_peer.seq_changed" wnl 168 [(169, 169)] []
  | .getPeerAipsNestFail => d "get_peer.allowedips_nest_failed" wnl 172 [(173, 173)] [(175, 175)]
  | .getPeerAipIter => d "get_peer.allowedips_iterate" wnl 175 [(177, 181)] []
  | .getPeerAipFail => d "get_peer.get_allowedips_failed" wnl 181 [(182, 185)] []
  | .getStartErr => d "wg_get_device_start.lookup_error" wnl 204 [(205, 205)] [(206, 207)]
  | .dumpNoHdr => d "wg_get_device_dump.no_header" wnl 227 [(228, 228)] [(229, 229)]
  | .dumpFirst => d "wg_get_device_dump.first_part" wnl 231 [(232, 251)] []
  | .dumpPutPort => d "wg_get_device_dump.put_listen_port_failed" wnl 232 [] [(234, 234)]
  | .dumpPutFwmark => d "wg_get_device_dump.put_fwmark_failed" wnl 234 [] [(235, 235)]
  | .dumpPutIfindex => d "wg_get_device_dump.put_ifindex_failed" wnl 235 [] [(236, 236)]
  | .dumpPutIfname => d "wg_get_device_dump.put_ifname_failed" wnl 236 [] [(239, 240)]
  | .dumpHasIdentity => d "wg_get_device_dump.has_identity" wnl 240 [(241, 249)] []
  | .dumpPutPrivate => d "wg_get_device_dump.put_private_key_failed" wnl 241 [] [(244, 246)]
  | .dumpPutPublic => d "wg_get_device_dump.put_public_key_failed" wnl 244 [] []
  | .dumpNoPeersNest => d "wg_get_device_dump.no_peers_nest" wnl 255 [(256, 256)] [(257, 257)]
  | .dumpPeerListEmpty => d "wg_get_device_dump.peer_list_empty" wnl 264 [] [(265, 265)]
  | .dumpCursorSet => d "wg_get_device_dump.cursor_set" wnl 265 [] []
  | .dumpCursorDead => d "wg_get_device_dump.cursor_dead" wnl 265 [] []
  | .dumpPeerIter => d "wg_get_device_dump.peers_iterate" wnl 270 [(271, 275)] []
  | .dumpGetPeerFail => d "wg_get_device_dump.get_peer_failed" wnl 271 [(272, 273)] [(275, 275)]
  | .dumpOutRetZero => d "wg_get_device_dump.ret_zero" wnl 280 [] []
  | .dumpOutNotDone => d "wg_get_device_dump.not_done" wnl 280 [] []
  | .dumpOutHasCursor => d "wg_get_device_dump.has_cursor" wnl 280 [(281, 281)] []
  -- the compiler copies the `out:` tail per path; only the !done copy owns
  -- genlmsg_end's point (290), and 296's point is the shared epilogue
  | .dumpRetErr => d "wg_get_device_dump.ret_error" wnl 286 [(287, 288)] []
  -- see ret_error
  | .dumpDone => d "wg_get_device_dump.done" wnl 291 [(292, 293)] [(295, 295)]
  | .getDoneHasWg => d "wg_get_device_done.has_wg" wnl 308 [(309, 309)] []
  | .setPortSame => d "set_port.same_port" wnl 318 [(319, 319)] [(320, 320)]
  | .setPortPeerIter => d "set_port.peers_iterate" wnl 320 [(321, 321)] []
  | .setPortNotRunning => d "set_port.not_running" wnl 322 [(323, 324)] [(326, 326)]
  | .aipNoFamily => d "set_allowedip.no_family" wnl 335 [] []
  | .aipNoAddr => d "set_allowedip.no_ipaddr" wnl 335 [] []
  | .aipNoCidr => d "set_allowedip.no_cidr" wnl 336 [] [(338, 339)]
  | .aipV4Family => d "set_allowedip.inet" wnl 341 [] []
  | .aipV4Cidr => d "set_allowedip.cidr_le_32" wnl 341 [] []
  | .aipV4Len => d "set_allowedip.inet_length" wnl 342 [(343, 346)] []
  | .aipV6Family => d "set_allowedip.inet6" wnl 347 [] []
  | .aipV6Cidr => d "set_allowedip.cidr_le_128" wnl 347 [] []
  | .aipV6Len => d "set_allowedip.inet6_length" wnl 348 [(349, 352)] []
  | .peerHasPubkey => d "set_peer.has_public_key" wnl 365 [(366, 366)] []
  | .peerPubkeyLen => d "set_peer.public_key_length" wnl 366 [(367, 367)] []
  | .peerHasPsk => d "set_peer.has_preshared_key" wnl 370 [(371, 371)] []
  | .peerPskLen => d "set_peer.preshared_key_length" wnl 371 [(372, 372)] []
  | .peerHasFlags => d "set_peer.has_flags" wnl 374 [(375, 375)] []
  | .peerBadFlags => d "set_peer.unknown_flags" wnl 377 [(378, 378)] [(380, 381)]
  | .peerHasProtocol => d "set_peer.has_protocol_version" wnl 381 [(382, 383)] []
  | .peerBadProtocol => d "set_peer.protocol_version_not_1" wnl 382 [(383, 383)] []
  | .peerNotFound => d "set_peer.not_found" wnl 389 [(390, 421)] []
  | .peerNewRemoveOrUpdate => d "set_peer.new_remove_or_update_only" wnl 390 [(391, 391)] [(394, 397)]
  | .peerSelfHasIdentity => d "set_peer.device_has_identity" wnl 397 [(398, 400)] []
  | .peerSelfKeyMatch => d "set_peer.device_public_key" wnl 398 [(406, 408)] []
  | .peerCreateErr => d "set_peer.create_error" wnl 413 [(414, 416)] [(421, 421)]
  | .peerRemoveMe => d "set_peer.remove_me" wnl 424 [(425, 426)] [(429, 429)]
  | .peerSetPsk => d "set_peer.set_preshared_key" wnl 429 [(430, 433)] []
  | .peerHasEndpoint => d "set_peer.has_endpoint" wnl 436 [(437, 441)] []
  | .peerEndpointV4Len => d "set_peer.endpoint_inet_length" wnl 441 [] []
  | .peerEndpointV4Family => d "set_peer.endpoint_inet" wnl 441 [(442, 443)] []
  | .peerEndpointV6Len => d "set_peer.endpoint_inet6_length" wnl 444 [] []
  | .peerEndpointV6Family => d "set_peer.endpoint_inet6" wnl 444 [(445, 446)] []
  | .peerReplaceAips => d "set_peer.replace_allowedips" wnl 450 [(451, 452)] []
  | .peerHasAips => d "set_peer.has_allowedips" wnl 454 [(455, 466)] []
  | .peerAipsIter => d "set_peer.allowedips_iterate" wnl 458 [(459, 465)] []
  -- the compiler merges the `goto out` of 462 with that of 465
  | .peerAipParseErr => d "set_peer.allowedip_parse_error" wnl 461 [] [(463, 463)]
  | .peerAipErr => d "set_peer.set_allowedip_error" wnl 464 [(465, 465)] []
  | .peerHasKeepalive => d "set_peer.has_keepalive" wnl 469 [(470, 479)] []
  | .peerKeepaliveWasZero => d "set_peer.keepalive_was_zero" wnl 473 [(474, 474)] []
  | .peerKeepaliveNonzero => d "set_peer.keepalive_nonzero" wnl 474 [(475, 475)] []
  | .peerKeepaliveRunning => d "set_peer.keepalive_running" wnl 475 [] []
  | .peerSendKeepalive => d "set_peer.send_keepalive" wnl 478 [(479, 479)] []
  | .peerRunning => d "set_peer.running" wnl 482 [(483, 483)] []
  | .peerZeroPsk => d "set_peer.zero_preshared_key" wnl 487 [(488, 489)] []
  | .setDevLookupErr => d "wg_set_device.lookup_error" wnl 499 [(500, 501)] [(504, 505)]
  | .setDevHasFlags => d "wg_set_device.has_flags" wnl 507 [(508, 508)] []
  | .setDevBadFlags => d "wg_set_device.unknown_flags" wnl 510 [(511, 511)] [(513, 513)]
  | .setDevHasPort => d "wg_set_device.has_listen_port" wnl 513 [] []
  | .setDevHasFwmark => d "wg_set_device.has_fwmark" wnl 513 [] []
  | .setDevNoNet => d "wg_set_device.no_creating_net" wnl 517 [] []
  | .setDevNotCapable => d "wg_set_device.not_capable" wnl 517 [] []
  | .setDevPermErr => d "wg_set_device.permission_error" wnl 519 [(520, 520)] []
  | .setDevFwmark => d "wg_set_device.set_fwmark" wnl 525 [(526, 530)] []
  | .setDevFwmarkPeerIter => d "wg_set_device.fwmark_peers_iterate" wnl 529 [(530, 530)] []
  | .setDevPort => d "wg_set_device.set_listen_port" wnl 533 [(534, 537)] []
  | .setDevPortErr => d "wg_set_device.set_port_error" wnl 536 [(537, 537)] []
  | .setDevReplacePeers => d "wg_set_device.replace_peers" wnl 540 [(541, 541)] []
  | .setDevHasPrivateKey => d "wg_set_device.has_private_key" wnl 543 [(544, 545)] []
  | .setDevPrivateKeyLen => d "wg_set_device.private_key_length" wnl 544 [(546, 553)] []
  | .setDevKeyUnchanged => d "wg_set_device.private_key_unchanged" wnl 551 [(553, 553)] [(558, 558)]
  | .setDevGenPublic => d "wg_set_device.public_key_generated" wnl 558 [(559, 564)] []
  | .setDevOldPeer => d "wg_set_device.peer_with_new_public_key" wnl 561 [(562, 563)] []
  | .setDevSendStagedNoIdentity => d "wg_set_device.had_no_identity" wnl 568 [] []
  | .setDevSendStagedRunning => d "wg_set_device.running" wnl 568 [] []
  | .setDevSendStagedKept => d "wg_set_device.send_staged_packets" wnl 570 [] []
  | .setDevSendStagedHasIdentity => d "wg_set_device.has_identity" wnl 570 [] []
  | .setDevKeyPeerIter => d "wg_set_device.key_peers_iterate" wnl 573 [(574, 577)] []
  | .setDevSendStagedPeer => d "wg_set_device.send_staged_to_peer" wnl 576 [(577, 577)] []
  | .setDevHasPeers => d "wg_set_device.has_peers" wnl 583 [(584, 595)] []
  | .setDevPeersIter => d "wg_set_device.peers_iterate" wnl 587 [(588, 594)] []
  -- the compiler merges the `goto out` of 591 with that of 594
  | .setDevParseErr => d "wg_set_device.peer_parse_error" wnl 590 [] [(592, 592)]
  | .setDevSetPeerErr => d "wg_set_device.set_peer_error" wnl 593 [(594, 594)] []
  | .setDevZeroKey => d "wg_set_device.zero_private_key" wnl 604 [(605, 606)] []
  -- drivers/net/wireguard/allowedips.c
  | .findNodeNode => d "find_node.node" aip 116 [] []
  | .findNodePrefixMatches => d "find_node.prefix_matches" aip 116 [(117, 121)] []
  | .findNodeHasPeer => d "find_node.has_peer" aip 117 [(118, 118)] []
  | .findNodeFullLength => d "find_node.full_length" aip 119 [(120, 120)] [(121, 121)]
  | .lookupFound => d "lookup.found" aip 140 [(141, 143)] []
  | .lookupPeerGone => d "lookup.peer_gone" aip 142 [(143, 143)] []
  | .lookupDstV4 => d "wg_allowedips_lookup_dst.inet" aip 359 [(360, 360)] [(361, 363)]
  | .lookupDstV6 => d "wg_allowedips_lookup_dst.inet6" aip 361 [(362, 362)] [(363, 363)]
  -- drivers/net/wireguard/queueing.h
  | .checkProtoParsed => d "wg_check_packet_protocol.parsed" wqh 73 [] []
  | .checkProtoMatches => d "wg_check_packet_protocol.matches" wqh 73 [] []
  -- drivers/net/wireguard/device.c
  | .openHasInet => d "wg_open.has_inet_device" wdv 39 [(44, 45)] []
  | .openHasInet6 => d "wg_open.has_inet6_device" wdv 47 [(48, 48)] []
  | .openSocketError => d "wg_open.socket_init_error" wdv 52 [(53, 53)] [(54, 58)]
  | .openPeersIter => d "wg_open.peers_iterate" wdv 54 [(55, 57)] []
  | .openKeepalive => d "wg_open.persistent_keepalive" wdv 56 [(57, 57)] []
  | .xmitBadProtocol => d "wg_xmit.bad_protocol" wdv 147 [(148, 150)] [(153, 153)]
  | .xmitNoPeer => d "wg_xmit.no_peer" wdv 154 [(155, 162)] [(165, 165)]
  | .xmitNoPeerInet => d "wg_xmit.no_peer_inet" wdv 156 [(157, 158)] [(159, 161)]
  | .xmitNoPeerInet6 => d "wg_xmit.no_peer_inet6" wdv 159 [(160, 161)] []
  | .xmitEndpointNotInet => d "wg_xmit.endpoint_not_inet" wdv 166 [] []
  | .xmitEndpointNotInet6 => d "wg_xmit.endpoint_not_inet6" wdv 166 [(167, 170)] []
  | .xmitValidDst => d "wg_xmit.valid_dst" wdv 173 [] []
  | .xmitNotGso => d "wg_xmit.not_gso" wdv 176 [(177, 177)] [(179, 186)]
  | .xmitWalk => d "wg_xmit.segments_iterate" wdv 189 [(190, 203)] []
  | .xmitShareFailed => d "wg_xmit.share_check_failed" wdv 193 [(194, 194)] [(199, 203)]
  | .xmitStagedOverflow => d "wg_xmit.staged_overflow" wdv 211 [(212, 213)] []
  | .xmitErrorInet => d "wg_xmit.error_inet" wdv 226 [(227, 227)] [(228, 229)]
  | .xmitErrorInet6 => d "wg_xmit.error_inet6" wdv 228 [(229, 229)] []
  -- drivers/net/wireguard/send.c
  | .queuedNotRetry => d "wg_packet_send_queued_handshake_initiation.not_retry" wsd 58 [(59, 59)] []
  | .queuedNotExpired => d "wg_packet_send_queued_handshake_initiation.not_expired" wsd 66 [] [(68, 68)]
  | .queuedDead => d "wg_packet_send_queued_handshake_initiation.dead" wsd 68 [(69, 69)] [(71, 76)]
  | .queuedAlreadyQueued => d "wg_packet_send_queued_handshake_initiation.already_queued" wsd 75 [(80, 80)] []
  | .keepaliveStagedEmpty => d "wg_packet_send_keepalive.staged_empty" wsd 225 [(226, 236)] []
  | .keepaliveNoMem => d "wg_packet_send_keepalive.no_mem" wsd 228 [(229, 229)] [(230, 236)]
  | .stagedEmpty => d "wg_packet_send_staged_packets.empty" wsd 353 [(354, 354)] [(357, 361)]
  | .stagedNoKeypair => d "wg_packet_send_staged_packets.no_keypair" wsd 361 [(362, 362)] [(363, 363)]
  | .stagedOrphanWalk => d "wg_packet_send_staged_packets.orphan_iterate" wsd 399 [(400, 400)] []
  -- drivers/net/wireguard/noise.c
  | .keypairGetNull => d "wg_noise_keypair_get.null" wno 146 [] []
  | .keypairGetZero => d "wg_noise_keypair_get.refcount_zero" wno 146 [] [(148, 148)]
  -- drivers/net/wireguard/socket.c
  -- 320-325 run before the patch's kcov_remote_start on 326: no stream collects them
  | .rxNoSock => d "wg_receive.no_sock" wso 320 [(321, 321)] []
  -- 325-327's witness is the return address of `call wg_packet_receive` inside the
  -- remote section: wg_packet_receive ends by tail-jumping into the coverage hook
  | .rxNoWg => d "wg_receive.no_device" wso 323 [(324, 324)] [(325, 327)]
  -- drivers/net/wireguard/receive.c
  | .hdrTooShort => d "validate_header_len.too_short" wrc 30 [(31, 31)] [(32, 32)]
  | .hdrData => d "validate_header_len.data" wrc 32 [(33, 33)] []
  | .hdrDataLen => d "validate_header_len.data_length" wrc 33 [(34, 34)] []
  | .hdrInit => d "validate_header_len.initiation" wrc 35 [(36, 36)] []
  | .hdrInitLen => d "validate_header_len.initiation_length" wrc 36 [(37, 37)] []
  | .hdrResp => d "validate_header_len.response" wrc 38 [(39, 39)] []
  | .hdrRespLen => d "validate_header_len.response_length" wrc 39 [(40, 40)] []
  | .hdrCookie => d "validate_header_len.cookie" wrc 41 [(42, 42)] []
  | .hdrCookieLen => d "validate_header_len.cookie_length" wrc 42 [(43, 43)] []
  | .prepBadProtocol => d "prepare_skb_header.bad_protocol" wrc 52 [] [(53, 53)]
  | .prepTransportBelowHead => d "prepare_skb_header.transport_below_head" wrc 53 [] [(54, 55)]
  | .prepTransportBeyondTail => d "prepare_skb_header.transport_beyond_tail" wrc 54 [] [(57, 58)]
  | .prepOffsetTooBig => d "prepare_skb_header.offset_too_big" wrc 59 [] [(60, 60)]
  | .prepOffsetBeyondLen => d "prepare_skb_header.offset_beyond_len" wrc 60 [] [(65, 65)]
  | .prepUdpLenSmall => d "prepare_skb_header.udp_len_small" wrc 66 [] [(67, 67)]
  | .prepUdpLenLying => d "prepare_skb_header.udp_len_lying" wrc 67 [] [(72, 73)]
  | .prepPullFailed => d "prepare_skb_header.pull_failed" wrc 74 [] [(76, 76)]
  | .prepTrimFailed => d "prepare_skb_header.trim_failed" wrc 76 [] [(78, 78)]
  | .prepLenMismatch => d "prepare_skb_header.len_mismatch" wrc 79 [(80, 81)] [(82, 82)]
  | .prepNoHeaderLen => d "prepare_skb_header.no_header_len" wrc 83 [(84, 84)] [(85, 85)]
  | .prepPullHeaderFailed => d "prepare_skb_header.pull_header_failed" wrc 86 [(87, 87)] [(88, 89)]
  | .rxPrepareFailed => d "wg_packet_receive.prepare_failed" wrc 544 [(545, 545)] [(546, 546)]
  | .rxHandshake => d "wg_packet_receive.handshake" wrc 546 [(550, 572)] []
  | .rxData => d "wg_packet_receive.data" wrc 546 [(575, 577)] [(579, 580)]
  | .rxRngNotReady => d "wg_packet_receive.rng_not_ready" wrc 552 [(553, 553)] [(554, 554)]
  | .rxQueueBusy => d "wg_packet_receive.queue_busy" wrc 554 [(555, 558)] [(560, 560)]
  | .rxProduceFailed => d "wg_packet_receive.produce_failed" wrc 561 [(562, 565)] [(567, 571)]
  -- witnessed through 213's inline frames; 214-216 run after kcov_remote_stop
  | .workerConsumed => d "wg_packet_handshake_receive_worker.consumed" wrc 212 [(213, 216)] []
  | .hsCookie => d "wg_receive_handshake_packet.cookie" wrc 104 [(105, 109)] [(112, 113)]
  | .hsUnderLoad => d "wg_receive_handshake_packet.under_load" wrc 114 [(115, 115)] [(116, 116)]
  | .hsWasUnderLoad => d "wg_receive_handshake_packet.was_under_load" wrc 116 [(117, 119)] []
  | .hsLoadedOperand => d "wg_receive_handshake_packet.loaded_and_cookie" wrc 123 [] []
  | .hsLoadedCookieOk => d "wg_receive_handshake_packet.mac_with_cookie" wrc 123 [] []
  | .hsNotLoaded => d "wg_receive_handshake_packet.not_loaded" wrc 124 [] []
  -- not under load, the chain decides on this operand: 134 (the switch) runs iff
  -- it is true. Its false side owns no point here: GCC knows under_load is
  -- false and jumps past the `else if` at 126 to the drop.
  | .hsMacNoCookie => d "wg_receive_handshake_packet.mac_without_cookie" wrc 124 [(125, 125), (134, 134)] []
  | .hsNeedsCookieLoaded => d "wg_receive_handshake_packet.needs_cookie_loaded" wrc 126 [] []
  | .hsNeedsCookieMac => d "wg_receive_handshake_packet.needs_cookie_mac" wrc 126 [(127, 127)] []
  | .dataNoKeypair => d "wg_packet_consume_data.no_keypair" wrc 520 [(521, 521)] [(523, 523)]
  -- drivers/net/wireguard/cookie.c
  | .macInvalid => d "wg_cookie_validate_packet.mac1_invalid" wck 132 [(133, 133)] [(135, 135)]
  | .macNoCookieCheck => d "wg_cookie_validate_packet.no_cookie_check" wck 137 [(138, 138)] [(140, 140)]
  | .cookieLookupMiss => d "wg_cookie_message_consume.lookup_miss" wck 205 [(209, 209)] [(211, 211)]
  -- drivers/net/wireguard/peerlookup.c
  | .idxMatch => d "wg_index_hashtable_lookup.index_matches" wpl 211 [(212, 214)] []
  | .idxFound => d "wg_index_hashtable_lookup.found" wpl 217 [(218, 222)] []
  -- drivers/net/wireguard/queueing.h
  | .cpumaskWrap => d "wg_cpumask_next_online.wrap" wqh 128 [(129, 129)] []
  -- drivers/net/wireguard/noise.c
  | .msgEphemeralCopy => d "message_ephemeral.copy" wno 490 [(491, 491)] []
  | .kdfNoFirstDst => d "kdf.no_first_dst" wno 362 [] []
  | .kdfNoFirstLen => d "kdf.no_first_len" wno 362 [] [(366, 368)]
  | .kdfNoSecondDst => d "kdf.no_second_dst" wno 370 [] []
  | .kdfNoSecondLen => d "kdf.no_second_len" wno 370 [] [(374, 376)]
  | .kdfNoThirdDst => d "kdf.no_third_dst" wno 378 [] []
  | .kdfNoThirdLen => d "kdf.no_third_len" wno 378 [] [(382, 384)]
  | .mixDhNull => d "mix_dh.null_dh" wno 411 [(412, 412)] [(413, 415)]
  | .mixPrecomputedNull => d "mix_precomputed_dh.null" wno 424 [(425, 425)] [(426, 429)]
  | .msgDecryptFailed => d "message_decrypt.failed" wno 477 [(480, 480)] [(481, 482)]
  | .consumeNoIdentity => d "wg_noise_handshake_consume_initiation.no_identity" wno 599 [(600, 600)] [(602, 605)]
  | .consumeEsFailed => d "wg_noise_handshake_consume_initiation.es_failed" wno 608 [(609, 609)] [(612, 612)]
  | .consumeStaticFailed => d "wg_noise_handshake_consume_initiation.static_failed" wno 612 [(614, 614)] [(617, 617)]
  | .consumeNoPeer => d "wg_noise_handshake_consume_initiation.no_peer" wno 618 [(619, 619)] [(620, 624)]
  -- ss succeeded: the inlined mix_precomputed_dh's kdf block (frame line 623,
  -- not covered when ss fails). In this build no KCOV point is attributed to
  -- the timestamp decryption at 628 before its result is known.
  | .consumeSsFailed => d "wg_noise_handshake_consume_initiation.ss_failed" wno 623 [(625, 625)] [(623, 623)]
  | .consumeTimestampFailed => d "wg_noise_handshake_consume_initiation.timestamp_failed" wno 628 [(630, 630)] [(632, 636)]
  | .consumeReplay => d "wg_noise_handshake_consume_initiation.replay" wno 639 [] []
  | .consumeFlood => d "wg_noise_handshake_consume_initiation.flood" wno 639 [] [(643, 644)]
  | .consumeNewerTimestamp => d "wg_noise_handshake_consume_initiation.newer_timestamp" wno 645 [(646, 646)] []
  | .consumeLaterTime => d "wg_noise_handshake_consume_initiation.later_consumption" wno 651 [(652, 652)] []
  | .consumeFailedPut => d "wg_noise_handshake_consume_initiation.failed_put" wno 662 [(663, 663)] []
  | .respNotConsumed => d "wg_noise_handshake_create_response.not_consumed" wno 681 [(682, 682)] [(684, 685)]
  | .respNoEphemeral => d "wg_noise_handshake_create_response.no_ephemeral" wno 689 [(691, 691)] [(692, 694)]
  | .respEeFailed => d "wg_noise_handshake_create_response.ee_failed" wno 697 [(699, 699)] [(702, 702)]
  | .respSeFailed => d "wg_noise_handshake_create_response.se_failed" wno 702 [(704, 704)] [(707, 708)]
  | .keypairCreateNoMem => d "keypair_create.no_mem" wno 102 [(103, 103)] [(104, 109)]
  -- `a && b`: the continuation (827) follows both a=0 and a=1,b=0
  | .sessionNotCreatedResponse => d "wg_noise_handshake_begin_session.not_created_response" wno 823 [(824, 824)] []
  | .sessionNotConsumedResponse => d "wg_noise_handshake_begin_session.not_consumed_response" wno 824 [(825, 825)] []
  | .sessionNoKeypair => d "wg_noise_handshake_begin_session.no_keypair" wno 828 [(829, 829)] [(830, 834)]
  | .sessionInitiator => d "wg_noise_handshake_begin_session.initiator" wno 834 [(835, 836)] [(838, 839)]
  | .sessionAlive => d "wg_noise_handshake_begin_session.alive" wno 843 [(845, 852)] [(854, 854)]
  | .addKeypairInitiator => d "add_new_keypair.initiator" wno 210 [(211, 238)] [(245, 248)]
  -- drivers/net/wireguard/cookie.c
  | .addMacCookieValid => d "wg_cookie_add_mac_to_packet.cookie_valid" wck 170 [(171, 171)] []
  | .addMacCookieFresh => d "wg_cookie_add_mac_to_packet.cookie_fresh" wck 171 [(173, 174)] []
  -- drivers/net/wireguard/send.c
  | .respCreated => d "wg_packet_send_handshake_response.created" wsd 94 [(95, 106)] []
  | .respSessionBegun => d "wg_packet_send_handshake_response.session_begun" wsd 96 [(98, 105)] []
  -- drivers/net/wireguard/receive.c
  | .hsSwitchInitiation => d "wg_receive_handshake_packet.initiation" wrc 134 [(135, 155)] []
  | .hsSwitchResponse => d "wg_receive_handshake_packet.response" wrc 134 [(158, 188)] []
  | .hsInitNeedsCookie => d "wg_receive_handshake_packet.initiation_needs_cookie" wrc 139 [(140, 142)] [(144, 144)]
  | .hsInitNoPeer => d "wg_receive_handshake_packet.initiation_no_peer" wrc 145 [(146, 148)] [(150, 155)]
  | .hsWrongPacket => d "wg_receive_handshake_packet.wrong_packet" wrc 192 [(193, 194)] [(197, 203)]
  -- drivers/net/wireguard/socket.c
  | .epFromSkbOk => d "wg_socket_set_peer_endpoint_from_skb.endpoint_ok" wso 304 [(305, 305)] []
  | .epFromSkbInet => d "wg_socket_endpoint_from_skb.inet" wso 239 [(240, 244)] [(245, 245)]
  | .epFromSkbInet6 => d "wg_socket_endpoint_from_skb.inet6" wso 245 [(246, 250)] [(253, 253)]
  -- drivers/net/wireguard/timers.c
  | .modTimerRunning => d "mod_peer_timer.running" wtm 35 [(36, 36)] []
  | .modTimerAlive => d "mod_peer_timer.alive" wtm 36 [(37, 37)] []
  | .traversalKeepalive => d "wg_timers_any_authenticated_packet_traversal.keepalive" wtm 214 [(215, 216)] []
  -- D2 interface: timer state read on the data paths
  | .timersDataSentNotPending => d "wg_timers_data_sent.not_pending" wtm 147 [(148, 150)] []
  | .timersDataReceivedRunning => d "wg_timers_data_received.running" wtm 156 [(157, 157)] []
  | .timersDataReceivedNotPending => d "wg_timers_data_received.not_pending" wtm 157 [(158, 159)] [(161, 161)]
  | .keypairPutUnreferenceNow => d "wg_noise_keypair_put.unreference_now" wno 135 [(136, 138)] []
  | .keypairKrefPutReleased => d "wg_noise_keypair_put.kref_put_released" wno 139 [(119, 128)] []
  | .sendBufNoMem => d "wg_socket_send_buffer_to_peer.no_mem" wso 194 [(195, 195)] [(197, 200)]
  | .sendSkbInet => d "wg_socket_send_skb_to_peer.inet" wso 174 [(175, 176)] [(177, 177)]
  | .sendSkbInet6 => d "wg_socket_send_skb_to_peer.inet6" wso 177 [(178, 179)] [(181, 181)]
  | .sendSkbOk => d "wg_socket_send_skb_to_peer.sent" wso 182 [(183, 183)] []
  -- the early return at 27 shares the function's epilogue: no witness
  | .initRateLimited => d "wg_packet_send_handshake_initiation.rate_limited" wsd 25 [] [(29, 33)]
  | .initCreated => d "wg_packet_send_handshake_initiation.created" wsd 34 [(35, 42)] []
  | .initNoIdentity => d "wg_noise_handshake_create_initiation.no_identity" wno 532 [(533, 533)] [(535, 541)]
  | .initNoEphemeral => d "wg_noise_handshake_create_initiation.no_ephemeral" wno 542 [(544, 544)] [(545, 547)]
  | .initEsFailed => d "wg_noise_handshake_create_initiation.es_failed" wno 550 [(552, 552)] [(555, 557)]
  | .initSsFailed => d "wg_noise_handshake_create_initiation.ss_failed" wno 560 [(562, 562)] [(565, 574)]
  | .idxInsWalk1 => d "wg_index_hashtable_insert.unlocked_entry" wpl 133 [(136, 136)] []
  | .idxInsCollide1 => d "wg_index_hashtable_insert.unlocked_collision" wpl 136 [(138, 138)] []
  | .idxInsWalk2 => d "wg_index_hashtable_insert.locked_entry" wpl 145 [(148, 148)] []
  | .idxInsCollide2 => d "wg_index_hashtable_insert.locked_collision" wpl 148 [(149, 151)] []
  | .idxWalk => d "wg_index_hashtable_lookup.entry" wpl 209 [(211, 211)] []
  | .idxTypeMatch => d "wg_index_hashtable_lookup.type_matches" wpl 212 [(213, 213)] []
  | .idxPeerAlive => d "wg_index_hashtable_lookup.peer_alive" wpl 219 [(220, 220)] [(222, 222)]
  | .idxReplaceUnhashed => d "wg_index_hashtable_replace.unhashed" wpl 174 [(175, 175)] [(177, 186)]
  -- D1 stream B
  -- wg_noise_handshake_consume_response (noise.c:727-814); each `goto fail`
  -- jumps to the shared wg_peer_put at 804
  | .crespNoIdentity => d "wg_noise_handshake_consume_response.no_identity" wno 744 [(745, 745)] [(747, 749)]
  | .crespNoHandshake => d "wg_noise_handshake_consume_response.no_handshake" wno 750 [(751, 751)] [(753, 761)]
  | .crespNotCreatedInitiation => d "wg_noise_handshake_consume_response.not_created_initiation" wno 763 [(764, 764)] [(767, 767)]
  | .crespEeFailed => d "wg_noise_handshake_consume_response.ee_failed" wno 770 [(771, 771)] [(774, 774)]
  | .crespSeFailed => d "wg_noise_handshake_consume_response.se_failed" wno 774 [(775, 775)] [(778, 778)]
  -- the success side runs the down_write and the recheck (786-790), which own
  -- no KCOV point in the net-choice build: decrypt_failed=0 has no witness of
  -- its own there (the recheck's outcome spans do)
  | .crespDecryptFailed => d "wg_noise_handshake_consume_response.decrypt_failed" wno 781 [(783, 783)] [(786, 790)]
  | .crespStateChanged => d "wg_noise_handshake_consume_response.state_changed" wno 790 [(791, 792)] [(794, 801)]
  -- add_new_keypair's initiator arm (noise.c:215-233)
  | .addKeypairHasNext => d "add_new_keypair.has_next_keypair" wno 215 [(225, 228)] [(232, 233)]
  -- the response arm of wg_receive_handshake_packet (receive.c:157-188)
  | .hsRespNeedsCookie => d "wg_receive_handshake_packet.response_needs_cookie" wrc 161 [(162, 164)] [(166, 166)]
  | .hsRespNoPeer => d "wg_receive_handshake_packet.response_no_peer" wrc 167 [(168, 170)] [(172, 176)]
  | .hsRespSessionBegun => d "wg_receive_handshake_packet.response_session_begun" wrc 176 [(178, 186)] []
  -- D1 stream C: drivers/net/wireguard/send.c
  -- both `goto out_nokey`/`out_invalid` targets are shared with other exits
  | .stagedKeyInvalid => d "wg_packet_send_staged_packets.key_invalid" wsd 363 [] [(365, 365)]
  | .stagedBirthdateExpired => d "wg_packet_send_staged_packets.birthdate_expired" wsd 365 [] [(374, 388)]
  | .stagedNonceIterate => d "wg_packet_send_staged_packets.nonce_iterate" wsd 374 [(378, 381)] [(385, 388)]
  | .stagedNonceRejected => d "wg_packet_send_staged_packets.nonce_rejected" wsd 381 [] []
  -- the `goto err` and the returns share the epilogue at 325
  | .createDataDead => d "wg_packet_create_data.dead" wsd 317 [] [(320, 320)]
  | .createDataEpipe => d "wg_packet_create_data.epipe" wsd 322 [(323, 323)] []
  | .createDataOk => d "wg_packet_create_data.ok" wsd 326 [] []
  | .createDataOkEpipe => d "wg_packet_create_data.ok_epipe" wsd 326 [] [(328, 330)]
  | .padNoMtu => d "calculate_skb_padding.no_mtu" wsd 145 [(146, 146)] [(154, 159)]
  | .padOverMtu => d "calculate_skb_padding.over_mtu" wsd 154 [(155, 155)] []
  -- encrypt_packet's `return false` exits share the epilogue
  -- `return false` at 184 shares the function's epilogue (covered on success)
  | .encCowHeadFailed => d "encrypt_packet.cow_head_failed" wsd 183 [] [(187, 187)]
  | .encChecksumPartial => d "encrypt_packet.checksum_partial" wsd 187 [] []
  | .encChecksumHelpFailed => d "encrypt_packet.checksum_help_failed" wsd 188 [] []
  | .encCowDataFailed => d "encrypt_packet.cow_data_failed" wsd 193 [] []
  | .encTooManyFrags => d "encrypt_packet.too_many_frags" wsd 193 [] [(199, 213)]
  | .encSgvecFailed => d "encrypt_packet.sgvec_failed" wsd 213 [] [(216, 218)]
  | .encWorkerConsumed => d "wg_packet_encrypt_worker.consumed" wsd 293 [(294, 307)] []
  -- the walk's exit and its `break` both reach 305
  | .encWorkerSkbIterate => d "wg_packet_encrypt_worker.skb_iterate" wsd 296 [(297, 303)] []
  | .encWorkerEncrypted => d "wg_packet_encrypt_worker.encrypted" wsd 297 [(299, 299)] [(301, 302)]
  | .encWorkerNeedResched => d "wg_packet_encrypt_worker.need_resched" wsd 306 [(307, 307)] []
  | .txPacket => d "wg_packet_tx_worker.packet" wsd 269 [(270, 270)] []
  | .txNotUncrypted => d "wg_packet_tx_worker.not_uncrypted" wsd 270 [(272, 283)] []
  | .txCrypted => d "wg_packet_tx_worker.crypted" wsd 275 [(276, 276)] [(278, 278)]
  | .txNeedResched => d "wg_packet_tx_worker.need_resched" wsd 282 [(283, 283)] []
  | .doneSkbIterate => d "wg_packet_create_data_done.skb_iterate" wsd 249 [(250, 253)] [(256, 259)]
  -- `!send(...) && !is_keepalive` (251-252): the first operand's sides are
  -- the call's continuation either way
  | .doneSendOk => d "wg_packet_create_data_done.sent" wsd 251 [] []
  | .doneNotKeepalive => d "wg_packet_create_data_done.not_keepalive" wsd 252 [(253, 253)] []
  -- keep_key_fresh (259) follows either way
  | .doneDataSent => d "wg_packet_create_data_done.data_sent" wsd 256 [(257, 257)] []
  -- `keypair && is_valid && (counter > REKEY_AFTER_MESSAGES || (initiator &&
  -- expired))` (131-134): each operand's true side evaluates the next line
  | .freshKeypair => d "keep_key_fresh.keypair" wsd 131 [] []
  | .freshValid => d "keep_key_fresh.valid" wsd 131 [(132, 132)] []
  | .freshCounter => d "keep_key_fresh.counter" wsd 132 [] [(133, 133)]
  | .freshInitiator => d "keep_key_fresh.initiator" wsd 133 [(134, 134)] []
  | .freshExpired => d "keep_key_fresh.birthdate_expired" wsd 134 [] []
  | .freshSend => d "keep_key_fresh.send" wsd 137 [(138, 138)] []
  -- D1 stream C: drivers/net/wireguard/queueing.h
  | .enqueuePeerQueueFull => d "wg_queue_enqueue_per_device_and_peer.peer_queue_full" wqh 167 [(168, 168)] [(173, 176)]
  | .enqueueRingFull => d "wg_queue_enqueue_per_device_and_peer.ring_full" wqh 174 [(175, 175)] [(176, 176)]
  -- `cpu >= nr_cpu_ids || !cpumask_test_cpu(cpu, cpu_online_mask)`: DWARF puts
  -- the bit test (evaluated iff the first operand is false) on 109; the body
  -- follows either operand
  | .chooseCpuInvalid => d "wg_cpumask_choose_online.cpu_invalid" wqh 109 [] [(109, 109)]
  | .chooseCpuOffline => d "wg_cpumask_choose_online.cpu_offline" wqh 110 [] []
  | .chooseCpuIndexIterate => d "wg_cpumask_choose_online.index_iterate" wqh 113 [(114, 114)] []
  | .prevQueuePeeked => d "wg_prev_queue_peek.peeked" wqh 145 [(146, 146)] [(147, 148)]
  -- D2 stream B: wg_packet_consume_data (receive.c:509-540). The `goto err`
  -- targets are shared with other exits.
  | .dataPeerDead => d "wg_packet_consume_data.peer_dead" wrc 523 [(524, 524)] [(526, 527)]
  | .dataEpipe => d "wg_packet_consume_data.epipe" wrc 528 [(529, 529)] []
  -- `likely(!ret || ret == -EPIPE)` (530): the operands share the line
  | .dataEnqueueOk => d "wg_packet_consume_data.enqueued" wrc 530 [(531, 532)] []
  | .dataEnqueueOkEpipe => d "wg_packet_consume_data.enqueued_epipe" wrc 530 [] [(535, 535)]
  -- decrypt_packet (receive.c:242-292): the `return false` exits share the
  -- epilogue; in `a || b || c` (252-254) each operand's false side
  -- evaluates the next line; the body (255-256) follows any operand
  -- `return false` (250) is the shared epilogue
  | .decNoKeypair => d "decrypt_packet.no_keypair" wrc 249 [] []
  | .decKeyInvalid => d "decrypt_packet.key_invalid" wrc 252 [] [(253, 253)]
  | .decKeyExpired => d "decrypt_packet.key_expired" wrc 253 [] [(254, 254)]
  | .decCounterLimit => d "decrypt_packet.counter_limit" wrc 254 [] [(259, 260)]
  | .decCowDataFailed => d "decrypt_packet.cow_data_failed" wrc 271 [] []
  | .decTooManyFrags => d "decrypt_packet.too_many_frags" wrc 271 [] [(274, 275)]
  | .decSgvecFailed => d "decrypt_packet.sgvec_failed" wrc 275 [] [(278, 280)]
  | .decDecryptFailed => d "decrypt_packet.decrypt_failed" wrc 278 [] [(286, 287)]
  | .decTrimFailed => d "decrypt_packet.trim_failed" wrc 287 [] [(289, 289)]
  -- wg_packet_decrypt_worker (receive.c:493-507)
  | .decWorkerConsumed => d "wg_packet_decrypt_worker.consumed" wrc 499 [(500, 503)] []
  | .decWorkerDecrypted => d "wg_packet_decrypt_worker.decrypted" wrc 501 [] []
  | .decWorkerNeedResched => d "wg_packet_decrypt_worker.need_resched" wrc 504 [(505, 505)] []
  -- counter_validate (receive.c:295-331): the `goto out`s share the unlock
  | .ctrRejectCounter => d "counter_validate.counter_at_limit" wrc 302 [] [(303, 303)]
  | .ctrRejectTheirs => d "counter_validate.theirs_at_limit" wrc 303 [] [(306, 308)]
  | .ctrTooOld => d "counter_validate.too_old" wrc 308 [] [(312, 314)]
  | .ctrAdvance => d "counter_validate.advance" wrc 314 [(315, 321)] []
  | .ctrClearIter => d "counter_validate.clear_iterate" wrc 318 [(319, 320)] []
  -- wg_packet_rx_poll (receive.c:438-491): `goto next` joins at 478
  | .rxPollNoBudget => d "wg_packet_rx_poll.no_budget" wrc 448 [(449, 449)] []
  | .rxPollPacket => d "wg_packet_rx_poll.packet" wrc 451 [(452, 452)] []
  | .rxPollNotUncrypted => d "wg_packet_rx_poll.not_uncrypted" wrc 452 [(454, 456)] []
  | .rxPollNotCrypted => d "wg_packet_rx_poll.not_crypted" wrc 458 [] [(461, 461)]
  | .rxPollCounterInvalid => d "wg_packet_rx_poll.counter_invalid" wrc 461 [] [(470, 470)]
  | .rxPollEndpointFailed => d "wg_packet_rx_poll.endpoint_failed" wrc 470 [] [(473, 475)]
  | .rxPollFree => d "wg_packet_rx_poll.free" wrc 480 [(481, 481)] []
  | .rxPollBudgetDone => d "wg_packet_rx_poll.budget_done" wrc 483 [(484, 484)] []
  | .rxPollComplete => d "wg_packet_rx_poll.complete" wrc 487 [(488, 488)] []
  -- wg_packet_consume_data_done (receive.c:335-436); the dishonest labels
  -- (415-435) are shared by several gotos
  | .doneReceivedNew => d "wg_packet_consume_data_done.received_new" wrc 345 [(347, 348)] []
  -- keep_key_fresh (receive.c:220-240), receive.c's own static function
  | .rxFreshSentLastminute => d "keep_key_fresh.sent_lastminute" wrc 225 [(226, 226)] [(228, 229)]
  | .rxFreshKeypair => d "keep_key_fresh.rx_keypair" wrc 230 [] []
  | .rxFreshValid => d "keep_key_fresh.rx_valid" wrc 230 [(231, 231)] []
  | .rxFreshInitiator => d "keep_key_fresh.rx_initiator" wrc 231 [(232, 233)] []
  | .rxFreshExpired => d "keep_key_fresh.rx_birthdate_expired" wrc 232 [] []
  | .rxFreshSend => d "keep_key_fresh.rx_send" wrc 236 [(237, 238)] []
  | .doneRxKeepalive => d "wg_packet_consume_data_done.keepalive" wrc 357 [(358, 362)] [(365, 365)]
  | .doneNetworkBelowHead => d "wg_packet_consume_data_done.network_below_head" wrc 367 [(368, 368)] []
  -- `!(may_pull(iphdr) && (version == 4 || (version == 6 && may_pull(ipv6hdr))))`
  -- (369-372): the operands' sides are the next operand or the shared exits
  | .doneMayPullV4 => d "wg_packet_consume_data_done.may_pull_iphdr" wrc 369 [] []
  | .doneVersion4 => d "wg_packet_consume_data_done.version_4" wrc 370 [] []
  | .doneVersion6 => d "wg_packet_consume_data_done.version_6" wrc 371 [] []
  | .doneMayPullV6 => d "wg_packet_consume_data_done.may_pull_ipv6hdr" wrc 372 [] []
  | .doneProtoIp => d "wg_packet_consume_data_done.protocol_ip" wrc 385 [(386, 389)] [(390, 390)]
  | .doneV4TooShort => d "wg_packet_consume_data_done.ip_len_too_short" wrc 387 [(388, 388)] [(389, 389)]
  | .doneProtoIpv6 => d "wg_packet_consume_data_done.protocol_ipv6" wrc 390 [(391, 393)] [(395, 395)]
  | .doneLenBeyond => d "wg_packet_consume_data_done.len_beyond_skb" wrc 398 [(399, 399)] [(400, 401)]
  | .doneTrimFailed => d "wg_packet_consume_data_done.trim_failed" wrc 401 [(402, 402)] [(404, 405)]
  | .doneDishonestPeer => d "wg_packet_consume_data_done.dishonest_peer" wrc 408 [(409, 409)] [(411, 413)]
  -- wg_noise_received_with_keypair (noise.c:253-291)
  | .receivedNotNew => d "wg_noise_received_with_keypair.not_new" wno 262 [(263, 263)] [(265, 265)]
  -- `return true` (290) shares the epilogue with `return false` (263)
  | .receivedChanged => d "wg_noise_received_with_keypair.changed" wno 269 [(272, 273)] [(280, 289)]
  -- wg_allowedips_lookup_src (allowedips.c:367-375)
  | .lookupSrcV4 => d "wg_allowedips_lookup_src.inet" aip 370 [(371, 371)] [(372, 374)]
  | .lookupSrcV6 => d "wg_allowedips_lookup_src.inet6" aip 372 [(373, 373)] [(374, 374)]
  -- INET_ECN_decapsulate and __INET_ECN_decapsulate (inet_ecn.h:251-284),
  -- inlined into wg_packet_consume_data_done (receive.c:389, 393): compiled
  -- without a KCOV point in this build (correspondence/kcov.json lists them
  -- as branch-free), so no witnesses
  | .ecnDecapInnerNotEct => d "__INET_ECN_decapsulate.inner_not_ect" ech 253 [] []
  | .ecnDecapOuterNotEct => d "__INET_ECN_decapsulate.outer_not_ect" ech 254 [] []
  | .ecnDecapRcZero => d "INET_ECN_decapsulate.rc_zero" ech 276 [] []
  | .ecnDecapSetCe => d "INET_ECN_decapsulate.set_ce" ech 277 [] []
  | .ecnDecapOuterEct1 => d "INET_ECN_decapsulate.outer_ect1" ech 279 [] []
  -- D2 stream A: `ip_tunnel_ecn_encap(0, ip_hdr(skb), skb)` (send.c:378):
  -- ip_tunnel_get_dsfield's `skb_protocol(skb, true)` is vlan_get_protocol,
  -- whose `eth_type_vlan(type)` test (one decision for the two-case switch)
  -- opens the VLAN walk; then the IPv4 and IPv6 tests; then
  -- INET_ECN_encapsulate's `INET_ECN_is_ce(inner)`, whose two arms share
  -- line 49 (no witness)
  | .vlanTypeIsVlan => d "__vlan_get_protocol_offset.vlan_type" vlh 612 [(613, 628)] []   -- line 612: the condition line the build has as a statement (609 is not one)
  | .dsfieldIp => d "ip_tunnel_get_dsfield.ip" iph 560 [(561, 561)] [(562, 562)]
  | .dsfieldIpv6 => d "ip_tunnel_get_dsfield.ipv6" iph 562 [(563, 563)] [(565, 565)]
  | .ecnEncapInnerCe => d "INET_ECN_encapsulate.inner_ce" ech 49 [] []
  -- `padded_size = min(PACKET_CB(skb)->mtu, ALIGN(last_unit, ...))`
  -- (send.c:157-158): min()'s comparison, true when the MTU is the smaller
  -- (a branch-free select: no witness)
  | .padClamped => d "calculate_skb_padding.clamped" wsd 157 [] []
  -- P stream 2 (begin): fs/pipe.c, include/linux/pipe_fs_i.h, fs/fcntl.c,
  -- fs/read_write.c (docs/2026-10-05-p-pipes.md section 11, Appendix A)
  -- `page_count(page) == 1 && !pipe->tmp_page`: the operands share line 125 and the else arm (128)
  | .anonBufReleaseSole => d "anon_pipe_buf_release.page_count_one" "fs/pipe.c" 125 [] []
  | .anonBufReleaseNoTmp => d "anon_pipe_buf_release.no_tmp_page" "fs/pipe.c" 125 [(126, 126)] []
  | .pipeBufConfirmNoConfirm => d "pipe_buf_confirm.no_confirm" "include/linux/pipe_fs_i.h" 230 [(231, 231)] [(232, 232)]
  | .pipeReadNull => d "pipe_read.null_read" "fs/pipe.c" 260 [(261, 261)] [(263, 279)]
  -- `!pipe_empty(head, tail)`: the inlined `head == tail` is recorded at 305 (no inline frame)
  | .pipeReadNotEmpty => d "pipe_read.not_empty" "fs/pipe.c" 305 [(306, 350)] []
  | .pipeReadCharsOver => d "pipe_read.chars_over_total" "fs/pipe.c" 311 [(312, 317)] []
  | .pipeReadWhole => d "pipe_read.whole" "fs/pipe.c" 312 [(313, 315)] [(317, 317)]
  | .pipeReadConfirmError => d "pipe_read.confirm_error" "fs/pipe.c" 321 [(322, 324)] [(327, 328)]
  | .pipeReadShortCopy => d "pipe_read.short_copy" "fs/pipe.c" 328 [(329, 331)] [(333, 335)]
  | .pipeReadFaultNoRet => d "pipe_read.fault_no_ret" "fs/pipe.c" 329 [(330, 330)] []
  | .pipeReadPacket => d "pipe_read.packet" "fs/pipe.c" 338 [(339, 340)] []
  | .pipeReadBufEmpty => d "pipe_read.buf_empty" "fs/pipe.c" 343 [(344, 344)] []
  | .pipeReadDone => d "pipe_read.total_done" "fs/pipe.c" 346 [(347, 347)] [(348, 349)]
  | .pipeReadMore => d "pipe_read.more" "fs/pipe.c" 348 [(349, 349)] []
  | .pipeReadNoWriters => d "pipe_read.no_writers" "fs/pipe.c" 352 [(353, 353)] [(354, 354)]
  | .pipeReadHaveData => d "pipe_read.have_data" "fs/pipe.c" 354 [(355, 355)] [(356, 356)]
  -- `(f_flags & O_NONBLOCK) || (ki_flags & IOCB_NOWAIT)` over 356-357; DWARF puts both tests at 356
  | .pipeReadNonblock => d "pipe_read.o_nonblock" "fs/pipe.c" 356 [] [(357, 357)]
  | .pipeReadNowait => d "pipe_read.iocb_nowait" "fs/pipe.c" 357 [(358, 359)] [(361, 395)]
  | .pipeReadEmptyAtEnd => d "pipe_read.empty_at_end" "fs/pipe.c" 397 [(398, 398)] []
  | .pipeReadWasFull => d "pipe_read.was_full" "fs/pipe.c" 401 [(402, 402)] []
  | .pipeReadWakeNextReader => d "pipe_read.wake_next_reader" "fs/pipe.c" 403 [(404, 404)] []
  | .pipeReadPositive => d "pipe_read.ret_positive" "fs/pipe.c" 406 [(407, 407)] []
  | .pipeWriteNull => d "pipe_write.null_write" "fs/pipe.c" 452 [(453, 453)] [(455, 455)]
  | .pipeWriteNoReaders => d "pipe_write.no_readers" "fs/pipe.c" 457 [(458, 460)] [(471, 473)]
  -- `chars && !was_empty`: the operands share line 474
  | .pipeWriteChars => d "pipe_write.chars" "fs/pipe.c" 474 [] []
  | .pipeWriteNotWasEmpty => d "pipe_write.not_was_empty" "fs/pipe.c" 474 [(475, 494)] []
  -- the merge test over 479-480; DWARF puts `offset + chars <= PAGE_SIZE` at 479
  | .pipeWriteCanMerge => d "pipe_write.can_merge" "fs/pipe.c" 479 [] []
  | .pipeWriteFits => d "pipe_write.fits" "fs/pipe.c" 480 [(481, 493)] []
  | .pipeWriteMergeConfirmErr => d "pipe_write.merge_confirm_error" "fs/pipe.c" 482 [(483, 483)] [(485, 485)]
  | .pipeWriteMergeShort => d "pipe_write.merge_short_copy" "fs/pipe.c" 486 [(487, 488)] [(491, 492)]
  | .pipeWriteMergeDone => d "pipe_write.merge_done" "fs/pipe.c" 492 [(493, 493)] []
  | .pipeWriteLoopNoReaders => d "pipe_write.loop_no_readers" "fs/pipe.c" 498 [(499, 502)] [(505, 506)]
  | .pipeWriteLoopNoRet => d "pipe_write.epipe_no_ret" "fs/pipe.c" 500 [(501, 501)] []
  -- `!pipe_full(head, tail, max_usage)`: `head - tail >= max_usage`, recorded at 506
  | .pipeWriteNotFull => d "pipe_write.not_full" "fs/pipe.c" 506 [(507, 550)] []
  | .pipeWriteNoTmpPage => d "pipe_write.no_tmp_page" "fs/pipe.c" 512 [(513, 518)] []
  | .pipeWriteAllocFailed => d "pipe_write.alloc_failed" "fs/pipe.c" 514 [(515, 516)] [(518, 518)]
  -- `ret = ret ? : -ENOMEM`: a select
  | .pipeWriteAllocRet => d "pipe_write.alloc_failed_ret" "fs/pipe.c" 515 [] []
  -- `is_packetized(filp)` (411-414, `f_flags & O_DIRECT`), inlined with its test recorded at 534;
  -- is_packetized owns no instrumentation point of its own
  | .pipeWritePacketized => d "pipe_write.packetized" "fs/pipe.c" 534 [(535, 535)] [(537, 537)]
  -- `copied < PAGE_SIZE && iov_iter_count(from)`: the operands share line 541, and 546 runs
  -- after either false outcome
  | .pipeWriteShortCopy => d "pipe_write.short_copy" "fs/pipe.c" 541 [] []
  | .pipeWriteShortCopyLeft => d "pipe_write.short_copy_count" "fs/pipe.c" 541 [(542, 544)] []
  | .pipeWriteFaultNoRet => d "pipe_write.fault_no_ret" "fs/pipe.c" 542 [(543, 543)] []
  | .pipeWriteDone => d "pipe_write.done" "fs/pipe.c" 549 [(550, 550)] []
  -- `!pipe_full(head, ...)` with the local `head` read at 505: after a slot is inserted
  -- (`pipe->head = head + 1`, 526) it is one behind (design Appendix A, audit)
  | .pipeWriteStaleNotFull => d "pipe_write.not_full_stale_head" "fs/pipe.c" 553 [(554, 554)] [(557, 557)]
  -- `(f_flags & O_NONBLOCK) || (ki_flags & IOCB_NOWAIT)` over 557-558; DWARF puts both tests at 557
  | .pipeWriteNonblock => d "pipe_write.o_nonblock" "fs/pipe.c" 557 [] [(558, 558)]
  | .pipeWriteNowait => d "pipe_write.iocb_nowait" "fs/pipe.c" 558 [(559, 561)] [(563, 582)]
  | .pipeWriteNoRet => d "pipe_write.eagain_no_ret" "fs/pipe.c" 559 [(560, 560)] []
  | .pipeWriteFullAtOut => d "pipe_write.full_at_out" "fs/pipe.c" 585 [(586, 586)] []
  -- `was_empty || pipe->poll_usage`: the operands share line 601 and the body (602)
  | .pipeWriteWasEmpty => d "pipe_write.was_empty" "fs/pipe.c" 601 [] []
  | .pipeWritePollUsage => d "pipe_write.poll_usage" "fs/pipe.c" 601 [] []
  | .pipeWriteWakeNextWriter => d "pipe_write.wake_next_writer" "fs/pipe.c" 604 [(605, 605)] []
  -- `ret > 0 && sb_start_write_trylock(...)`: the operands share line 606; the trylock is a cut
  -- returning success (design section 5)
  | .pipeWritePositive => d "pipe_write.ret_positive" "fs/pipe.c" 606 [] []
  | .pipeWriteSbTrylock => d "pipe_write.sb_start_write_trylock" "fs/pipe.c" 606 [(607, 610)] []
  | .pipeWriteUpdateTimeErr => d "pipe_write.update_time_error" "fs/pipe.c" 608 [(609, 609)] []
  -- put_pipe_info and pipe_release run once per __fput: twice in the -EMFILE unwind (design section 4)
  | .putPipeInfoLast => d "put_pipe_info.last_file" "fs/pipe.c" 712 [(713, 714)] []
  | .putPipeInfoKill => d "put_pipe_info.kill" "fs/pipe.c" 718 [(719, 719)] []
  | .pipeReleaseRead => d "pipe_release.fmode_read" "fs/pipe.c" 728 [(729, 729)] []
  | .pipeReleaseWrite => d "pipe_release.fmode_write" "fs/pipe.c" 730 [(731, 731)] []
  -- `!pipe->readers != !pipe->writers`: two zero tests and an xor, not one comparison (design section 10)
  | .pipeReleaseOneSide => d "pipe_release.one_side_left" "fs/pipe.c" 734 [(735, 738)] []
  -- `soft_limit && user_bufs > soft_limit`: one line, a returned value
  | .tooManySoftLimit => d "too_many_pipe_buffers_soft.limit_set" "fs/pipe.c" 775 [] []
  | .tooManySoftOver => d "too_many_pipe_buffers_soft.over_limit" "fs/pipe.c" 775 [] []
  | .tooManyHardLimit => d "too_many_pipe_buffers_hard.limit_set" "fs/pipe.c" 782 [] []
  | .tooManyHardOver => d "too_many_pipe_buffers_hard.over_limit" "fs/pipe.c" 782 [] []
  -- `!capable(CAP_SYS_RESOURCE) && !capable(CAP_SYS_ADMIN)`: `capable` is a cut returning true
  -- for root (design section 5); alloc_pipe_info may call it at 807 and 812
  | .unprivNoResource => d "pipe_is_unprivileged_user.not_cap_sys_resource" "fs/pipe.c" 787 [] []
  | .unprivNoAdmin => d "pipe_is_unprivileged_user.not_cap_sys_admin" "fs/pipe.c" 787 [] []
  | .allocPipeInfoNoMem => d "alloc_pipe_info.kzalloc_failed" "fs/pipe.c" 799 [(800, 800)] [(802, 802)]
  -- `pipe_bufs * PAGE_SIZE > max_size` with `pipe_bufs` the constant 16: folded to
  -- `max_size < 65536`, the variable on the left (design Appendix A)
  | .allocPipeInfoOverMax => d "alloc_pipe_info.def_over_max_size" "fs/pipe.c" 802 [] []
  | .allocPipeInfoNotCapable => d "alloc_pipe_info.not_capable" "fs/pipe.c" 802 [(803, 803)] []
  | .allocPipeInfoSoft => d "alloc_pipe_info.soft_exceeded" "fs/pipe.c" 807 [] []
  | .allocPipeInfoSoftUnpriv => d "alloc_pipe_info.soft_unprivileged" "fs/pipe.c" 807 [(808, 809)] []
  | .allocPipeInfoHard => d "alloc_pipe_info.hard_exceeded" "fs/pipe.c" 812 [] []
  | .allocPipeInfoHardUnpriv => d "alloc_pipe_info.hard_unprivileged" "fs/pipe.c" 812 [(813, 813)] []
  | .allocPipeInfoBufs => d "alloc_pipe_info.bufs_allocated" "fs/pipe.c" 818 [(819, 828)] [(832, 835)]
  -- `i < pipe->ring_size`: the rotated loop tests `ring_size != 0` first, a constant
  -- comparison the mirror's `(i, ring_size)` would not match, so no operands
  | .freePipeInfoLoop => d "free_pipe_info.slot_iterate" "fs/pipe.c" 850 [(851, 853)] [(859, 859)]
  | .freePipeInfoBufOps => d "free_pipe_info.buf_ops" "fs/pipe.c" 852 [(853, 853)] []
  | .freePipeInfoTmpPage => d "free_pipe_info.tmp_page" "fs/pipe.c" 859 [(860, 860)] []
  | .getPipeInodeNoInode => d "get_pipe_inode.no_inode" "fs/pipe.c" 885 [(886, 886)] [(888, 888)]
  | .getPipeInodeNoPipe => d "get_pipe_inode.no_pipe" "fs/pipe.c" 891 [(892, 892)] [(894, 909)]
  | .createPipeFilesNoInode => d "create_pipe_files.no_inode" "fs/pipe.c" 926 [(927, 927)] [(929, 929)]
  -- `watch_queue_init` is the -ENOPKG stub (CONFIG_WATCH_QUEUE unset): `if (error)` at 931 is folded
  | .createPipeFilesNotification => d "create_pipe_files.notification_pipe" "fs/pipe.c" 929 [(930, 935)] [(938, 940)]
  | .createPipeFilesWriterErr => d "create_pipe_files.writer_error" "fs/pipe.c" 941 [(942, 944)] [(947, 950)]
  | .createPipeFilesReaderErr => d "create_pipe_files.reader_error" "fs/pipe.c" 952 [(953, 955)] [(957, 962)]
  | .doPipeFlagsInvalid => d "__do_pipe_flags.invalid_flags" "fs/pipe.c" 970 [(971, 971)] [(973, 973)]
  | .doPipeFlagsCreateErr => d "__do_pipe_flags.create_error" "fs/pipe.c" 974 [(975, 975)] [(977, 977)]
  | .doPipeFlagsFdrErr => d "__do_pipe_flags.fdr_error" "fs/pipe.c" 978 [(979, 979)] [(980, 982)]
  | .doPipeFlagsFdwErr => d "__do_pipe_flags.fdw_error" "fs/pipe.c" 983 [(984, 984)] [(985, 993)]
  | .doPipe2Ok => d "do_pipe2.no_error" "fs/pipe.c" 1025 [(1026, 1035)] []
  | .doPipe2CopyFault => d "do_pipe2.copy_to_user_failed" "fs/pipe.c" 1026 [(1027, 1031)] [(1033, 1034)]
  | .roundPipeSizeTooBig => d "round_pipe_size.too_big" "fs/pipe.c" 1249 [(1250, 1250)] [(1253, 1253)]
  | .roundPipeSizeSmall => d "round_pipe_size.below_page" "fs/pipe.c" 1253 [(1254, 1254)] [(1256, 1256)]
  | .resizeRingNoMem => d "pipe_resize_ring.kcalloc_failed" "fs/pipe.c" 1273 [(1274, 1274)] [(1276, 1282)]
  | .resizeRingBusy => d "pipe_resize_ring.busy" "fs/pipe.c" 1282 [(1283, 1285)] [(1292, 1292)]
  | .resizeRingNonEmpty => d "pipe_resize_ring.non_empty" "fs/pipe.c" 1292 [(1293, 1305)] []
  | .resizeRingNoWrap => d "pipe_resize_ring.h_after_t" "fs/pipe.c" 1295 [(1296, 1297)] [(1299, 1304)]
  | .resizeRingHeadPart => d "pipe_resize_ring.h_nonzero" "fs/pipe.c" 1300 [(1301, 1302)] []
  -- dead in this build: 1320 stores `max_usage` unconditionally, so the compiler dropped the test
  -- (no comparison record, no point); still the C's choice point
  | .resizeRingShrinkMaxUsage => d "pipe_resize_ring.shrink_max_usage" "fs/pipe.c" 1314 [] []
  | .pipeSetSizeZero => d "pipe_set_size.no_slots" "fs/pipe.c" 1347 [(1348, 1348)] [(1357, 1357)]
  -- `nr_slots > max_usage && size > pipe_max_size && !capable(...)` over 1357-1358; DWARF puts
  -- both comparisons at 1357
  | .pipeSetSizeGrowMax => d "pipe_set_size.grow_check_max" "fs/pipe.c" 1357 [] []
  | .pipeSetSizeOverMax => d "pipe_set_size.over_max_size" "fs/pipe.c" 1358 [] []
  | .pipeSetSizeNotCapable => d "pipe_set_size.not_capable" "fs/pipe.c" 1358 [(1359, 1359)] []
  | .pipeSetSizeGrowLimits => d "pipe_set_size.grow_check_limits" "fs/pipe.c" 1363 [] []
  | .pipeSetSizeHard => d "pipe_set_size.hard_exceeded" "fs/pipe.c" 1364 [] []
  | .pipeSetSizeSoft => d "pipe_set_size.soft_exceeded" "fs/pipe.c" 1365 [] []
  | .pipeSetSizeUnpriv => d "pipe_set_size.unprivileged" "fs/pipe.c" 1366 [(1367, 1368)] []
  | .pipeSetSizeResizeErr => d "pipe_set_size.resize_error" "fs/pipe.c" 1372 [(1373, 1373)] [(1375, 1375)]
  -- `file->f_op != &pipefifo_fops || !pipe`: one line; `for_splice && ...` (1392) folds away
  | .getPipeInfoNotPipe => d "get_pipe_info.not_pipefifo" "fs/pipe.c" 1390 [] []
  | .getPipeInfoNoPipe => d "get_pipe_info.no_pipe" "fs/pipe.c" 1390 [] [(1394, 1394)]
  | .pipeFcntlNoPipe => d "pipe_fcntl.no_pipe" "fs/pipe.c" 1403 [(1404, 1404)] [(1406, 1406)]
  | .pipeFcntlSetSize => d "pipe_fcntl.case_f_setpipe_sz" "fs/pipe.c" 1409 [(1410, 1411)] []
  | .pipeFcntlGetSize => d "pipe_fcntl.case_f_getpipe_sz" "fs/pipe.c" 1412 [(1413, 1414)] []
  | .fcntlCasePipeSz => d "do_fcntl.case_f_setpipe_sz" fc 538 [(539, 541)] []
  | .killFasyncList => d "kill_fasync.has_list" fc 1151 [(1152, 1154)] []
  | .newSyncWriteQueued => d "new_sync_write.eiocbqueued" rw 591 [] []
  -- `ret > 0 && ppos`: one line; `ppos` is NULL for FMODE_STREAM files
  | .newSyncWritePositive => d "new_sync_write.ret_positive" rw 592 [] []
  | .newSyncWritePpos => d "new_sync_write.ppos" rw 592 [(593, 593)] []
  -- fs/file_table.c, called only by create_pipe_files on these paths
  | .allocFileCloneOk => d "alloc_file_clone.ok" ft 433 [(434, 435)] []
  -- P stream 2 (end)
  -- P stream 3 (begin): fs/inode.c, include/linux/time64.h, include/linux/fs.h,
  -- fs/libfs.c
  -- P stream 3 (end)
  -- P stream 2 signal (begin): kernel/signal.c
  -- `__si_special(priv)`: a select between SEND_SIG_PRIV and SEND_SIG_NOINFO
  | .sendSigPriv => d "send_sig.priv" "kernel/signal.c" 1675 [] []
  -- `!valid_signal(sig)`: `sig <= _NSIG` (include/linux/signal.h:274), recorded at 1662
  | .sendSigInfoInvalid => d "send_sig_info.invalid_signal" "kernel/signal.c" 1662 [(1663, 1663)] [(1665, 1665)]
  | .doSendSigLock => d "do_send_sig_info.lock_task_sighand" "kernel/signal.c" 1303 [(1304, 1305)] []
  | .sendSignalLockedNoinfo => d "send_signal_locked.noinfo" "kernel/signal.c" 1221 [(1222, 1223)] [(1224, 1249)]
  | .sendSignalLockedPriv => d "send_signal_locked.priv" "kernel/signal.c" 1224 [(1225, 1226)] [(1227, 1249)]
  | .sendSignalNotPrepared => d "__send_signal_locked.not_prepared" "kernel/signal.c" 1084 [(1085, 1085)] [(1087, 1087)]
  -- `pending = (type != PIDTYPE_PID) ? ...`: a select
  | .sendSignalShared => d "__send_signal_locked.shared_pending" "kernel/signal.c" 1087 [] []
  -- `(sig < SIGRTMIN) && sigismember(&signals->signal, sig)`: one line, a returned value
  | .legacyQueueNotRt => d "legacy_queue.not_rt" "kernel/signal.c" 1070 [] []
  | .legacyQueuePending => d "legacy_queue.pending" "kernel/signal.c" 1070 [] []
  | .sendSignalLegacy => d "__send_signal_locked.legacy_queue" "kernel/signal.c" 1094 [(1095, 1095)] [(1097, 1101)]
  -- `(sig == SIGKILL) || (t->flags & PF_KTHREAD)`: one line
  | .sendSignalSigkill => d "__send_signal_locked.sigkill" "kernel/signal.c" 1101 [] []
  | .sendSignalKthread => d "__send_signal_locked.kthread" "kernel/signal.c" 1101 [] [(1113, 1118)]
  -- no comparison record at 1113 (the compare is shared with 1101's): not declared one
  | .sendSignalNotRt => d "__send_signal_locked.not_rt" "kernel/signal.c" 1113 [(1114, 1114)] [(1116, 1116)]
  -- `is_si_special(info) || info->si_code >= 0`: one line, assigned
  | .sendSignalSiSpecial => d "__send_signal_locked.si_special" "kernel/signal.c" 1114 [] []
  | .sendSignalQueued => d "__send_signal_locked.queued" "kernel/signal.c" 1120 [(1121, 1146)] [(1148, 1164)]
  | .sendSignalNoinfo => d "__send_signal_locked.case_noinfo" "kernel/signal.c" 1123 [(1124, 1135)] []
  | .sendSignalPrivInfo => d "__send_signal_locked.case_priv" "kernel/signal.c" 1136 [(1137, 1143)] []
  | .sendSignalOverflowNotSpecial => d "__send_signal_locked.overflow_not_special" "kernel/signal.c" 1148 [] []
  | .sendSignalMultiprocess => d "__send_signal_locked.multiprocess" "kernel/signal.c" 1171 [(1172, 1182)] [(1184, 1184)]
  -- `signal->flags` is not mirrored (the trace child is not exiting): not declared a comparison
  | .prepareSignalGroupExit => d "prepare_signal.group_exit" "kernel/signal.c" 908 [(909, 914)] [(915, 915)]
  | .prepareSignalStop => d "prepare_signal.kernel_stop" "kernel/signal.c" 915 [(916, 922)] [(923, 923)]
  | .prepareSignalCont => d "prepare_signal.sigcont" "kernel/signal.c" 923 [(924, 964)] []
  -- `sigismember(&t->blocked, sig) || sigismember(&t->real_blocked, sig)`: one line, one body
  | .sigIgnoredBlocked => d "sig_ignored.blocked" "kernel/signal.c" 111 [] []
  | .sigIgnoredRealBlocked => d "sig_ignored.real_blocked" "kernel/signal.c" 111 [] [(119, 122)]
  | .sigIgnoredPtrace => d "sig_ignored.ptraced" "kernel/signal.c" 119 [(120, 120)] [(122, 122)]
  | .completeSignalWants => d "complete_signal.wants_signal" "kernel/signal.c" 1004 [(1005, 1005)] [(1006, 1006)]
  | .wantsSignalBlocked => d "wants_signal.blocked" "kernel/signal.c" 979 [(980, 980)] [(982, 991)]
  -- `(type == PIDTYPE_PID) || thread_group_empty(p)`: one line, one body
  | .completeSignalPidType => d "complete_signal.pid_type" "kernel/signal.c" 1006 [] []
  | .sigqueueAllocNoUcounts => d "__sigqueue_alloc.no_ucounts" "kernel/signal.c" 425 [(426, 426)] [(428, 428)]
  -- `override_rlimit || likely(sigpending <= task_rlimit(...))`: one line, one body
  | .sigqueueAllocOverride => d "__sigqueue_alloc.override_rlimit" "kernel/signal.c" 428 [] []
  | .sigqueueAllocNull => d "__sigqueue_alloc.q_null" "kernel/signal.c" 434 [(435, 435)] [(437, 439)]
  -- P stream 2 signal (end)

/-- The relation of a C value comparison, as written in the source
    (`lhs rel rhs`); `flag` is a mask test `(x & MASK)` against zero. -/
inductive Rel where
  | lt | le | gt | ge | eq | ne | flag
  deriving Repr, BEq

def Rel.name : Rel → String
  | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge" | .eq => "eq" | .ne => "ne" | .flag => "flag"

/-- A declared value comparison: the relation, and whether the right-hand
    operand is a compile-time constant. -/
structure Comparison where
  rel : Rel
  constRhs : Bool
  /-- The line DWARF attributes the comparison to, when it differs from the
      operand's source line (multi-line conditions); `none` means `line`. -/
  site : Option Nat := none
  /-- The comparison's value is assigned to a local that the condition tests
      (`x = a > b; ... if (... || x)`): the site precedes the condition. -/
  assigned : Bool := false

/-- The decisions that are value comparisons. Exactly these report operands
    (`branchCmp`, as `(lhs, rhs)` in source order); the check requires it. -/
def Decision.comparison : Decision → Option Comparison
  -- `(s64)last_initiation_consumption + NSEC_PER_SEC / INITIATIONS_PER_SECOND >
  -- (s64)ktime_get_coarse_boottime_ns()` is assigned to flood_attack at
  -- noise.c:635-637 (DWARF puts the compare at 635); the condition at 639
  -- tests flood_attack
  | .consumeFlood => some ⟨.gt, false, some 635, true⟩
  | .allocFdCloexec => some ⟨.flag, true, none, false⟩
  | .placementCidrLe => some ⟨.le, false, none, false⟩
  | .placementExact => some ⟨.eq, false, none, false⟩
  | .addCidrTooLong => some ⟨.gt, false, none, false⟩
  | .peerCreateMaxPeers => some ⟨.ge, true, none, false⟩
  | .refcountAddFromZero => some ⟨.eq, true, none, false⟩
  | .refcountAddNzZero => some ⟨.eq, true, none, false⟩
  | .allocFdExpandError => some ⟨.lt, true, none, false⟩
  | .allocFdExpanded => some ⟨.ne, true, none, false⟩
  | .allocFdLimit => some ⟨.ge, false, none, false⟩
  | .allocFdSearch => some ⟨.lt, false, none, false⟩
  | .allocFdUpdateNextFd => some ⟨.le, false, none, false⟩
  | .closeFdOutOfRange => some ⟨.ge, false, none, false⟩
  | .ctxDoReadSemaphore => some ⟨.flag, true, none, false⟩
  | .doDup2Cloexec => some ⟨.flag, true, none, false⟩
  | .doEventfdFdError => some ⟨.lt, true, none, false⟩
  | .doEventfdInvalidFlags => some ⟨.flag, true, none, false⟩
  | .dup3Equal => some ⟨.eq, false, none, false⟩
  | .dup3ExpandError => some ⟨.lt, true, none, false⟩
  | .dup3InvalidFlags => some ⟨.flag, true, none, false⟩
  | .dup3TargetLimit => some ⟨.ge, false, none, false⟩
  | .dupAllocOk => some ⟨.ge, true, none, false⟩
  | .eventfdFreeCtxHasId => some ⟨.ge, true, none, false⟩
  | .eventfdReadEmpty => some ⟨.eq, true, none, false⟩
  | .eventfdReadNonblock => some ⟨.flag, true, none, false⟩
  | .eventfdReadShort => some ⟨.lt, true, none, false⟩
  | .eventfdWriteBlocking => some ⟨.flag, true, none, false⟩
  | .eventfdWriteFits => some ⟨.gt, false, none, false⟩
  | .eventfdWriteReserved => some ⟨.eq, true, none, false⟩
  | .eventfdWriteWrongSize => some ⟨.ne, true, none, false⟩
  | .expandFilesFits => some ⟨.lt, false, none, false⟩
  | .fcntlPathFile => some ⟨.flag, true, none, false⟩
  | .fdInstallBacking => some ⟨.flag, true, none, false⟩
  | .fgetLightSingleOwner => some ⟨.eq, true, none, false⟩
  | .fileFreeAccounted => some ⟨.flag, true, none, false⟩
  | .fileFreeBacking => some ⟨.flag, true, none, false⟩
  | .fileInitPathModeRead => some ⟨.flag, true, none, false⟩
  | .fileInitPathModeWrite => some ⟨.flag, true, none, false⟩
  | .fileInitPathReadOnly => some ⟨.eq, true, none, false⟩
  | .filePposStream => some ⟨.flag, true, none, false⟩
  | .filpFlushCountZero => some ⟨.eq, true, none, false⟩
  | .filpFlushNotPath => some ⟨.flag, true, none, false⟩
  | .findNextFdAllFull => some ⟨.ge, false, none, false⟩
  | .fposLockAtomicPos => some ⟨.flag, true, none, false⟩
  | .fputFinalFasync => some ⟨.flag, true, none, false⟩
  | .fputFinalNeedUnmount => some ⟨.flag, true, none, false⟩
  | .fputFinalNotOpened => some ⟨.flag, true, none, false⟩
  | .getFileFromZero => some ⟨.eq, true, none, false⟩
  | .iocbFlagsAppend => some ⟨.flag, true, none, false⟩
  | .iocbFlagsDirect => some ⟨.flag, true, none, false⟩
  | .iocbFlagsDsync => some ⟨.flag, true, none, false⟩
  | .iocbFlagsSync => some ⟨.flag, true, none, false⟩
  | .ksysReadRetNonneg => some ⟨.ge, true, none, false⟩
  | .ksysWriteRetNonneg => some ⟨.ge, true, none, false⟩
  | .putFileAccessReadOnly => some ⟨.eq, true, none, false⟩
  | .putFileAccessWriter => some ⟨.flag, true, none, false⟩
  | .putUnusedFdLowerNextFd => some ⟨.lt, false, none, false⟩
  | .refcountSubPositive => some ⟨.gt, true, none, false⟩
  | .refcountSubToZero => some ⟨.eq, true, none, false⟩
  | .rwVerifyNegativeCount => some ⟨.lt, true, none, false⟩
  | .vfsReadCannotRead => some ⟨.flag, true, none, false⟩
  | .vfsReadNotReadable => some ⟨.flag, true, none, false⟩
  | .vfsWriteCannotWrite => some ⟨.flag, true, none, false⟩
  | .vfsWriteNotWritable => some ⟨.flag, true, none, false⟩
  | .setflAppendChanged => some ⟨.flag, true, none, false⟩
  | .setflNoatimeRequested => some ⟨.flag, true, none, false⟩
  | .setflNoatimeNotSet => some ⟨.flag, true, none, false⟩
  -- the three-line condition at fcntl.c:62-64: DWARF attributes `arg & O_DIRECT`
  -- to 62 and `f_mode & FMODE_CAN_ODIRECT` to 63, one line before their source
  | .setflDirect => some ⟨.flag, true, some 62, false⟩
  | .setflCannotOdirect => some ⟨.flag, true, some 63, false⟩
  | .setflFasyncChanged => some ⟨.flag, true, none, false⟩
  | .allocFdtableOverNrOpen => some ⟨.gt, false, none, false⟩
  | .expandFilesOverNrOpen => some ⟨.ge, false, none, false⟩
  | .setflAppendOnly => some ⟨.flag, true, none, false⟩
  | .setflNotOwnerOrCapable => some ⟨.eq, true, none, false⟩
  | .setflNotFifo => some ⟨.ne, true, none, false⟩
  | .allocFdtableBelowWanted => some ⟨.lt, false, none, false⟩
  | .allocFdtableOverIntMax => some ⟨.gt, true, none, false⟩
  | .copyFdtableShrink => some ⟨.lt, false, none, false⟩
  | .expandFdtableShared => some ⟨.gt, true, none, false⟩
  | .expandFdtableBugNr => some ⟨.lt, false, none, false⟩
  -- P stream 2 (begin): fs/pipe.c, include/linux/pipe_fs_i.h, fs/fcntl.c,
  -- fs/read_write.c (docs/2026-10-05-p-pipes.md section 11, Appendix A)
  | .anonBufReleaseSole => some ⟨.eq, true, none, false⟩
  | .pipeReadNull => some ⟨.eq, true, none, false⟩
  | .pipeReadNotEmpty => some ⟨.eq, false, none, false⟩
  | .pipeReadCharsOver => some ⟨.gt, false, none, false⟩
  | .pipeReadWhole => some ⟨.flag, true, none, false⟩
  | .pipeReadConfirmError => some ⟨.ne, true, none, false⟩
  | .pipeReadShortCopy => some ⟨.lt, false, none, false⟩
  | .pipeReadFaultNoRet => some ⟨.eq, true, none, false⟩
  | .pipeReadPacket => some ⟨.flag, true, none, false⟩
  | .pipeReadBufEmpty => some ⟨.eq, true, none, false⟩
  | .pipeReadDone => some ⟨.eq, true, none, false⟩
  | .pipeReadMore => some ⟨.eq, false, none, false⟩
  | .pipeReadNoWriters => some ⟨.eq, true, none, false⟩
  | .pipeReadHaveData => some ⟨.ne, true, none, false⟩
  | .pipeReadNonblock => some ⟨.flag, true, none, false⟩
  | .pipeReadNowait => some ⟨.flag, true, some 356, false⟩
  | .pipeReadEmptyAtEnd => some ⟨.eq, false, none, false⟩
  | .pipeReadPositive => some ⟨.gt, true, none, false⟩
  | .pipeWriteNull => some ⟨.eq, true, none, false⟩
  | .pipeWriteNoReaders => some ⟨.eq, true, none, false⟩
  | .pipeWriteChars => some ⟨.ne, true, none, false⟩
  | .pipeWriteCanMerge => some ⟨.flag, true, none, false⟩
  | .pipeWriteFits => some ⟨.le, true, some 479, false⟩
  | .pipeWriteMergeConfirmErr => some ⟨.ne, true, none, false⟩
  | .pipeWriteMergeShort => some ⟨.lt, false, none, false⟩
  | .pipeWriteMergeDone => some ⟨.eq, true, none, false⟩
  | .pipeWriteLoopNoReaders => some ⟨.eq, true, none, false⟩
  | .pipeWriteLoopNoRet => some ⟨.eq, true, none, false⟩
  | .pipeWriteNotFull => some ⟨.ge, false, none, false⟩
  | .pipeWriteAllocRet => some ⟨.ne, true, none, false⟩
  | .pipeWritePacketized => some ⟨.flag, true, none, false⟩
  | .pipeWriteShortCopy => some ⟨.lt, true, none, false⟩
  | .pipeWriteShortCopyLeft => some ⟨.ne, true, none, false⟩
  | .pipeWriteFaultNoRet => some ⟨.eq, true, none, false⟩
  | .pipeWriteDone => some ⟨.eq, true, none, false⟩
  | .pipeWriteStaleNotFull => some ⟨.ge, false, none, false⟩
  | .pipeWriteNonblock => some ⟨.flag, true, none, false⟩
  | .pipeWriteNowait => some ⟨.flag, true, some 557, false⟩
  | .pipeWriteNoRet => some ⟨.eq, true, none, false⟩
  | .pipeWriteFullAtOut => some ⟨.ge, false, none, false⟩
  | .pipeWritePositive => some ⟨.gt, true, none, false⟩
  | .pipeWriteUpdateTimeErr => some ⟨.ne, true, none, false⟩
  | .putPipeInfoLast => some ⟨.eq, true, none, false⟩
  | .pipeReleaseRead => some ⟨.flag, true, none, false⟩
  | .pipeReleaseWrite => some ⟨.flag, true, none, false⟩
  | .tooManySoftLimit => some ⟨.ne, true, none, false⟩
  | .tooManySoftOver => some ⟨.gt, false, none, false⟩
  | .tooManyHardLimit => some ⟨.ne, true, none, false⟩
  | .tooManyHardOver => some ⟨.gt, false, none, false⟩
  | .allocPipeInfoOverMax => some ⟨.lt, true, none, false⟩
  | .createPipeFilesNotification => some ⟨.flag, true, none, false⟩
  | .doPipeFlagsInvalid => some ⟨.flag, true, none, false⟩
  | .doPipeFlagsCreateErr => some ⟨.ne, true, none, false⟩
  | .doPipeFlagsFdrErr => some ⟨.lt, true, none, false⟩
  | .doPipeFlagsFdwErr => some ⟨.lt, true, none, false⟩
  | .doPipe2Ok => some ⟨.eq, true, none, false⟩
  | .roundPipeSizeTooBig => some ⟨.gt, true, none, false⟩
  | .roundPipeSizeSmall => some ⟨.lt, true, none, false⟩
  | .resizeRingBusy => some ⟨.lt, false, none, false⟩
  | .resizeRingNonEmpty => some ⟨.gt, true, none, false⟩
  | .resizeRingNoWrap => some ⟨.gt, false, none, false⟩
  | .resizeRingHeadPart => some ⟨.gt, true, none, false⟩
  | .pipeSetSizeZero => some ⟨.eq, true, none, false⟩
  | .pipeSetSizeGrowMax => some ⟨.gt, false, none, false⟩
  | .pipeSetSizeOverMax => some ⟨.gt, false, some 1357, false⟩
  | .pipeSetSizeGrowLimits => some ⟨.gt, false, none, false⟩
  | .pipeSetSizeResizeErr => some ⟨.lt, true, none, false⟩
  | .newSyncWritePositive => some ⟨.gt, true, none, false⟩
  -- P stream 2 (end)
  -- P stream 3 (begin): fs/inode.c, include/linux/time64.h, include/linux/fs.h,
  -- fs/libfs.c
  -- P stream 3 (end)
  -- P stream 2 signal (begin): kernel/signal.c
  | .sendSigPriv => some ⟨.ne, true, none, false⟩
  | .sendSigInfoInvalid => some ⟨.le, true, none, false⟩
  | .sendSignalShared => some ⟨.ne, true, none, false⟩
  | .legacyQueueNotRt => some ⟨.lt, true, none, false⟩
  | .sendSignalSigkill => some ⟨.eq, true, none, false⟩
  | .sendSignalMultiprocess => some ⟨.gt, true, none, false⟩
  | .prepareSignalCont => some ⟨.eq, true, none, false⟩
  | .completeSignalPidType => some ⟨.eq, true, none, false⟩
  | .sigqueueAllocOverride => some ⟨.ne, true, none, false⟩
  -- P stream 2 signal (end)
  | _ => none

/-- Decisions that one operation may evaluate more than once: those inside
    `alloc_fd`'s `repeat:` loop (evaluated again after a successful
    expansion), the refcount helpers, `fdget`/`fdput` (a WireGuard operation
    is two socket calls), and the WireGuard decisions under a loop over peers,
    allowed IPs or trie nodes. Only these may be reported more than
    once in one operation. -/
def Decision.repeatable : Decision → Bool
  | .allocFdBelowNextFd | .allocFdSearch | .findNextFdAllFull | .findNextFdSkipFullWords
  | .allocFdLimit | .expandFilesFits | .allocFdExpandError | .allocFdExpanded
  | .fgetLightSingleOwner | .fgetLightNoFile | .fgetLightMasked | .fdputFput
  | .swapEndian32 | .swapEndian128 | .pushRcuNonNull | .rootRemoveLenPositive | .rootRemovePopped
  | .rootRemoveHasPeer | .fls128High | .commonBits32 | .commonBits128 | .placementNode
  | .placementCidrLe | .placementPrefixMatches | .placementExact | .addCidrTooLong | .addNoPeer
  | .addEmptyTrie | .addRootNoMem | .addExact | .addNewnodeNoMem | .addNoParentNode
  | .addNoDown | .addNewnodeCoversDown | .addNewnodeAtRoot | .addIntermediateNoMem | .addIntermediateAtRoot
  | .removeListEmpty | .removeListIter | .removeHasBit0 | .removeHasBit1 | .removeChildExists
  | .removeLeafBit0 | .removeLeafBit1 | .removeParentIsNode | .removeParentNoPeer | .removeFreeParent
  | .removeNotFreeParent | .removeSiblingExists | .readNodeHasCidr | .refcountAddNzZero | .refcountAddNzRetry
  | .refcountAddNzNegative | .refcountAddNzWraps | .refcountAddFromZero | .refcountAddNegative | .refcountAddWraps
  | .genPublicNullSecret | .precomputeNoIdentity | .precomputeNullPoint | .handshakeInitHasPsk | .keypairPutNull
  | .expireNextKeypair | .expireCurrentKeypair | .peerCreateMaxPeers | .peerCreateNoMem | .peerCreateDstCacheFail
  | .peerGetMaybeZeroNull | .peerGetMaybeZeroDead | .peerRemoveNotDead | .peerRemoveNull | .peerRemoveAllIter1
  | .peerRemoveAllIter2 | .peerPutNull | .peerKrefPutReleased | .pubkeyLookupMatch | .eqA4
  | .eqB4 | .eqPort4 | .eqAddr4 | .eqSrc4 | .eqSrcIf4
  | .eqA6 | .eqB6 | .eqPort6 | .eqAddr6 | .eqScope6
  | .eqSrc6 | .eqANone | .eqBNone | .setEndpointEq | .setEndpointV4
  | .setEndpointV6 | .getAipNoNest | .getAipPutCidr | .getAipPutFamily | .getAipFamily6
  | .getAipPutAddr | .getPeerNoNest | .getPeerPubkeyFail | .getPeerFirst | .getPeerPskFail
  | .getPeerPutHandshake | .getPeerPutKeepalive | .getPeerPutTx | .getPeerPutRx | .getPeerPutProto
  | .getPeerEp4 | .getPeerEp6 | .getPeerEpFail | .getPeerNoAips | .getPeerSeqUnset
  | .getPeerSeqChanged | .getPeerAipsNestFail | .getPeerAipIter | .getPeerAipFail | .dumpPeerIter
  | .dumpGetPeerFail | .setPortPeerIter | .aipNoFamily | .aipNoAddr | .aipNoCidr
  | .aipV4Family | .aipV4Cidr | .aipV4Len | .aipV6Family | .aipV6Cidr
  | .aipV6Len | .peerHasPubkey | .peerPubkeyLen | .peerHasPsk | .peerPskLen
  | .peerHasFlags | .peerBadFlags | .peerHasProtocol | .peerBadProtocol | .peerNotFound
  | .peerNewRemoveOrUpdate | .peerSelfHasIdentity | .peerSelfKeyMatch | .peerCreateErr | .peerRemoveMe
  | .peerSetPsk | .peerHasEndpoint | .peerEndpointV4Len | .peerEndpointV4Family | .peerEndpointV6Len
  | .peerEndpointV6Family | .peerReplaceAips | .peerHasAips | .peerAipsIter | .peerAipParseErr
  | .peerAipErr | .peerHasKeepalive | .peerKeepaliveWasZero | .peerKeepaliveNonzero | .peerKeepaliveRunning
  | .peerSendKeepalive | .peerRunning | .peerZeroPsk | .setDevFwmarkPeerIter | .setDevKeyPeerIter
  | .setDevSendStagedPeer | .setDevPeersIter | .setDevParseErr | .setDevSetPeerErr | .refcountSubPositive
  | .refcountSubToZero | .refcountSubNonpositive | .refcountSubUnderflow
  | .findNodeNode | .findNodePrefixMatches | .findNodeHasPeer | .findNodeFullLength | .lookupFound
  | .lookupPeerGone | .checkProtoParsed | .checkProtoMatches | .openPeersIter | .openKeepalive
  | .xmitWalk | .xmitShareFailed | .xmitStagedOverflow | .queuedNotRetry | .queuedNotExpired
  | .queuedDead | .queuedAlreadyQueued | .keepaliveStagedEmpty | .keepaliveNoMem | .stagedEmpty
  | .stagedNoKeypair | .stagedOrphanWalk | .keypairGetNull | .keypairGetZero
  | .workerConsumed
  | .msgEphemeralCopy | .kdfNoFirstDst | .kdfNoFirstLen | .kdfNoSecondDst | .kdfNoSecondLen
  | .kdfNoThirdDst | .kdfNoThirdLen | .mixDhNull | .mixPrecomputedNull | .msgDecryptFailed
  | .timersDataSentNotPending | .timersDataReceivedRunning | .timersDataReceivedNotPending
  | .modTimerRunning | .modTimerAlive | .traversalKeepalive
  -- several send workers may run in one operation; bucket walks loop
  | .initRateLimited | .initCreated | .initNoIdentity | .initNoEphemeral | .initEsFailed | .initSsFailed
  | .idxInsWalk1 | .idxInsCollide1 | .idxInsWalk2 | .idxInsCollide2 | .idxWalk | .idxMatch
  | .sendBufNoMem | .sendSkbInet | .sendSkbInet6 | .sendSkbOk | .addMacCookieValid | .addMacCookieFresh
  -- D1 stream B: add_new_keypair and keypairs_clear put up to three live
  -- keypairs in one operation (stream C: the tx worker's put shares an
  -- operation with the receive path's)
  | .keypairPutUnreferenceNow | .keypairKrefPutReleased
  -- D1 stream C: per peer and per packet (loops over staged packets, ring
  -- items and tx-queue packets); the encrypt queue's wg_cpumask_next_online
  -- and the tx worker's keypair put share an operation with the receive path's
  | .stagedKeyInvalid | .stagedBirthdateExpired | .stagedNonceIterate | .stagedNonceRejected
  | .createDataDead | .createDataEpipe | .createDataOk | .createDataOkEpipe
  | .padNoMtu | .padOverMtu | .encCowHeadFailed | .encChecksumPartial | .encChecksumHelpFailed
  | .encCowDataFailed | .encTooManyFrags | .encSgvecFailed
  | .encWorkerConsumed | .encWorkerSkbIterate | .encWorkerEncrypted | .encWorkerNeedResched
  | .txPacket | .txNotUncrypted | .txCrypted | .txNeedResched
  | .doneSkbIterate | .doneSendOk | .doneNotKeepalive | .doneDataSent
  | .freshKeypair | .freshValid | .freshCounter | .freshInitiator | .freshExpired | .freshSend
  | .enqueuePeerQueueFull | .enqueueRingFull | .chooseCpuInvalid | .chooseCpuOffline | .chooseCpuIndexIterate
  | .prevQueuePeeked | .cpumaskWrap
  -- D2 stream B: the loops of the decrypt worker, the NAPI poll and
  -- counter_validate
  | .decWorkerConsumed | .decWorkerDecrypted | .decWorkerNeedResched
  | .rxPollPacket | .rxPollNotUncrypted | .rxPollNotCrypted | .rxPollCounterInvalid | .rxPollEndpointFailed
  | .rxPollFree | .rxPollBudgetDone | .ctrClearIter => true
  -- D2 stream A: per packet of a staged list
  | .vlanTypeIsVlan | .dsfieldIp | .dsfieldIpv6 | .ecnEncapInnerCe | .padClamped => true
  -- P interface (design section 4, audit M2): `pipe2` runs alloc_fd,
  -- alloc_empty_file, file_init_path, alloc_file and fd_install twice in one
  -- operation, and its -EMFILE unwind runs two fput/__fput in the same
  -- operation's task work. This loosens "reported once" for eventfd
  -- operations on these decisions [AGENT, accepted in the design].
  | .allocFdUpdateNextFd | .setOpenFdFullWord | .allocFdCloexec | .clearCloexecWasSet | .allocFdSlotNotNull
  | .putUnusedFdLowerNextFd
  | .fdInstallBacking | .fdInstallResizeInProgress | .fdInstallSlotBusy
  | .allocEmptyFileOverMax | .allocEmptyFileNotCapable | .allocEmptyFileNoMem
  | .iocbFlagsAppend | .iocbFlagsDirect | .iocbFlagsDsync | .iocbFlagsSync
  | .fileInitPathLlseek | .fileInitPathModeRead | .fileInitPathHasRead | .fileInitPathHasReadIter
  | .fileInitPathModeWrite | .fileInitPathHasWrite | .fileInitPathHasWriteIter | .fileInitPathReadOnly
  | .allocFileOk | .allocFilePseudoErr
  | .fputLast | .fputNotOpened | .fputInInterrupt | .fputKthread | .fputTaskWorkAddFailed
  | .fputFinalNotOpened | .fputFinalFasync | .fputFinalRelease | .fputFinalCharDevice | .fputFinalHasCdev
  | .fputFinalNotPath | .fputFinalNeedUnmount
  | .eventpollReleaseLinked | .fileOwnerRelease | .putFileAccessReadOnly | .putFileAccessWriter
  | .fileFreeAccounted | .fileFreeBacking => true
  -- P stream 2 (begin): fs/pipe.c, include/linux/pipe_fs_i.h, fs/fcntl.c,
  -- fs/read_write.c (docs/2026-10-05-p-pipes.md section 11, Appendix A)
  | .anonBufReleaseSole | .anonBufReleaseNoTmp | .pipeBufConfirmNoConfirm | .pipeReadNotEmpty
  | .pipeReadCharsOver | .pipeReadWhole | .pipeReadConfirmError | .pipeReadShortCopy | .pipeReadFaultNoRet
  | .pipeReadPacket | .pipeReadBufEmpty | .pipeReadDone | .pipeReadMore | .pipeReadNoWriters
  | .pipeReadHaveData | .pipeReadNonblock | .pipeReadNowait | .pipeWriteLoopNoReaders | .pipeWriteLoopNoRet
  | .pipeWriteNotFull | .pipeWriteNoTmpPage | .pipeWriteAllocFailed | .pipeWriteAllocRet
  | .pipeWritePacketized | .pipeWriteShortCopy | .pipeWriteShortCopyLeft | .pipeWriteFaultNoRet
  | .pipeWriteDone | .pipeWriteStaleNotFull | .pipeWriteNonblock | .pipeWriteNowait | .pipeWriteNoRet
  | .putPipeInfoLast | .putPipeInfoKill | .pipeReleaseRead | .pipeReleaseWrite | .pipeReleaseOneSide
  | .unprivNoResource | .unprivNoAdmin | .freePipeInfoLoop | .freePipeInfoBufOps | .killFasyncList => true
  -- P stream 2 (end)
  -- P stream 3 (begin): fs/inode.c, include/linux/time64.h, include/linux/fs.h,
  -- fs/libfs.c
  -- P stream 3 (end)
  -- P stream 2 signal (begin): kernel/signal.c
  -- P stream 2 signal (end)
  | _ => false

/-- Every decision, enumerated through the constructor index. -/
def Decision.all : List Decision :=
  (List.range 4096).filterMap fun i =>
    let x := Decision.ofNat i
    if x.ctorIdx == i then some x else none

def Step.label (s : Step) : String :=
  s!"{s.decision.info.label}={if s.outcome then 1 else 0}"

end Leanux
