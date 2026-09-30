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

/-- Why an outcome has no KCOV witness. The check requires a reason exactly
    for the sides whose spans own no instrumentation point in the built kernel,
    so a reason can neither be missing nor hide a witnessed side. -/
inductive Unobservable where
  /-- The outcome continues into code that the other outcome also runs. -/
  | sharedContinuation
  /-- A short-circuit operand whose line or body is shared with another operand. -/
  | sharedOperand
  /-- The C selects a value without a branch (compiled to a conditional move). -/
  | branchFree
  /-- The span's statements own no KCOV instrumentation point in this build. -/
  | noInstrumentation
  /-- The compiler attributes a block both outcomes run to the span's line; the
      span is narrowed (see the comment at the decision). -/
  | compilerShared
  /-- A `BUG_ON` arm: no code but the trap, and outside the modeled domain. -/
  | outsideDomain
  /-- The configured build folds the test to a constant (a constant argument,
      `CONFIG_MODULES=n`, or an empty arm such as compiled-out accounting). -/
  | constantFolded
  /-- The arm is a macro expansion on the condition's own line (`WARN_ONCE`). -/
  | sameLine
  /-- The next operand is evaluated in an inline helper defined elsewhere in the
      file (`fd_is_open`), outside the span window of this decision. -/
  | inlineHelper
  deriving Repr, BEq

def Unobservable.name : Unobservable → String
  | .sharedContinuation => "shared_continuation"
  | .sharedOperand => "shared_operand"
  | .branchFree => "branch_free"
  | .noInstrumentation => "no_instrumentation"
  | .compilerShared => "compiler_shared"
  | .outsideDomain => "outside_domain"
  | .constantFolded => "constant_folded"
  | .sameLine => "same_line"
  | .inlineHelper => "inline_helper"

/-- The declared reason, per decision and outcome; `none` means the outcome
    must be witnessed. -/
def Decision.unobservable : Decision → Bool → Option Unobservable
  | .eventfdFreeCtxHasId, false => some .sharedContinuation
  | .krefPutLast, false => some .sharedContinuation
  | .refcountSubPositive, true => some .sharedOperand
  | .refcountSubPositive, false => some .sharedOperand
  | .refcountSubToZero, false => some .sharedContinuation
  | .refcountSubNonpositive, true => some .sharedOperand
  | .refcountSubNonpositive, false => some .sharedOperand
  | .refcountSubUnderflow, true => some .sharedOperand
  | .refcountSubUnderflow, false => some .sharedOperand
  | .ctxDoReadSemaphore, true => some .branchFree
  | .ctxDoReadSemaphore, false => some .branchFree
  | .ctxDoReadCountNonzero, true => some .branchFree
  | .ctxDoReadCountNonzero, false => some .branchFree
  | .eventfdReadShort, true => some .noInstrumentation
  | .eventfdReadNonblock, true => some .sharedOperand
  | .eventfdReadNowait, true => some .sharedOperand
  | .eventfdReadWaitqueueActive, false => some .sharedContinuation
  | .eventfdReadCopyFault, true => some .noInstrumentation
  | .eventfdReadCopyFault, false => some .sharedContinuation
  | .eventfdWriteWrongSize, true => some .noInstrumentation
  | .eventfdWriteCopyFault, true => some .noInstrumentation
  | .eventfdWriteReserved, true => some .noInstrumentation
  | .eventfdWriteFits, true => some .noInstrumentation
  | .eventfdWriteBlocking, false => some .sharedContinuation
  | .eventfdWriteResPositive, false => some .sharedContinuation
  | .eventfdWriteWaitqueueActive, false => some .sharedContinuation
  | .doEventfdInvalidFlags, true => some .noInstrumentation
  | .doEventfdNoMem, true => some .noInstrumentation
  | .doEventfdFdError, true => some .noInstrumentation
  | .fileFreeAccounted, false => some .sharedContinuation
  | .allocEmptyFileOverMax, true => some .sharedOperand
  | .allocEmptyFileOverMax, false => some .sharedContinuation
  | .allocEmptyFileNotCapable, false => some .sharedContinuation
  | .allocEmptyFileNoMem, true => some .noInstrumentation
  | .iocbFlagsAppend, true => some .noInstrumentation
  | .iocbFlagsAppend, false => some .sharedContinuation
  | .iocbFlagsDirect, false => some .sharedContinuation
  | .iocbFlagsDsync, false => some .sharedContinuation
  | .iocbFlagsSync, false => some .sharedContinuation
  | .fileInitPathLlseek, false => some .sharedContinuation
  | .fileInitPathModeRead, false => some .sharedContinuation
  | .fileInitPathHasRead, true => some .sharedOperand
  | .fileInitPathHasRead, false => some .sharedOperand
  | .fileInitPathHasReadIter, true => some .sharedOperand
  | .fileInitPathHasReadIter, false => some .sharedOperand
  | .fileInitPathModeWrite, false => some .sharedContinuation
  | .fileInitPathHasWrite, true => some .sharedOperand
  | .fileInitPathHasWrite, false => some .sharedOperand
  | .fileInitPathHasWriteIter, true => some .sharedOperand
  | .fileInitPathHasWriteIter, false => some .sharedOperand
  | .fileInitPathReadOnly, false => some .sharedContinuation
  | .allocFileOk, false => some .sharedContinuation
  | .allocPathPseudoFail, true => some .noInstrumentation
  | .allocFilePseudoErr, false => some .sharedContinuation
  | .putFileAccessReadOnly, false => some .sharedContinuation
  | .putFileAccessWriter, false => some .sharedContinuation
  | .fputFinalNotOpened, true => some .noInstrumentation
  | .eventpollReleaseLinked, false => some .noInstrumentation
  | .fputFinalFasync, false => some .sharedContinuation
  | .fputFinalRelease, false => some .sharedContinuation
  | .fputFinalCharDevice, true => some .sharedOperand
  | .fputFinalCharDevice, false => some .sharedOperand
  | .fputFinalHasCdev, true => some .sharedOperand
  | .fputFinalHasCdev, false => some .sharedOperand
  | .fputFinalNotPath, false => some .sharedContinuation
  | .fileOwnerRelease, false => some .sharedContinuation
  | .fputFinalNeedUnmount, false => some .sharedContinuation
  | .fputLast, false => some .sharedContinuation
  | .fputInInterrupt, true => some .sharedOperand
  | .fputInInterrupt, false => some .sharedOperand
  | .fputKthread, true => some .sharedContinuation
  | .fputTaskWorkAddFailed, true => some .sharedContinuation
  | .fputTaskWorkAddFailed, false => some .noInstrumentation
  | .fputSyncLast, false => some .sharedContinuation
  | .filpFlushHasFlush, false => some .sharedContinuation
  | .filpFlushNotPath, false => some .sharedContinuation
  | .closeNoFile, true => some .noInstrumentation
  | .closeRestartSys, true => some .sharedOperand
  | .closeRestartSys, false => some .sharedOperand
  | .closeRestartNoIntr, true => some .sharedOperand
  | .closeRestartNoIntr, false => some .sharedOperand
  | .closeRestartNoHand, true => some .sharedOperand
  | .closeRestartNoHand, false => some .sharedOperand
  | .closeRestartBlock, true => some .noInstrumentation
  | .closeRestartBlock, false => some .sharedContinuation
  | .clearCloexecWasSet, false => some .sharedContinuation
  | .setOpenFdFullWord, true => some .compilerShared
  | .setOpenFdFullWord, false => some .sharedContinuation
  | .findNextFdAllFull, true => some .noInstrumentation
  | .findNextFdSkipFullWords, true => some .noInstrumentation
  | .findNextFdSkipFullWords, false => some .sharedContinuation
  | .expandFilesFits, true => some .noInstrumentation
  | .expandFilesOverNrOpen, true => some .noInstrumentation
  | .allocFdBelowNextFd, true => some .noInstrumentation
  | .allocFdBelowNextFd, false => some .sharedContinuation
  | .allocFdSearch, false => some .sharedContinuation
  | .allocFdLimit, true => some .noInstrumentation
  | .allocFdExpandError, true => some .noInstrumentation
  | .allocFdExpanded, true => some .noInstrumentation
  | .allocFdUpdateNextFd, false => some .sharedContinuation
  | .allocFdSlotNotNull, false => some .sharedContinuation
  | .putUnusedFdLowerNextFd, false => some .sharedContinuation
  | .fdInstallBacking, true => some .noInstrumentation
  | .fdInstallSlotBusy, true => some .outsideDomain
  | .closeFdOutOfRange, true => some .compilerShared
  | .closeFdFound, false => some .sharedContinuation
  | .getFileFromZero, true => some .sameLine
  | .getFileFromZero, false => some .sameLine
  | .doDup2NoTofree, false => some .sharedContinuation
  | .doDup2FdOpen, false => some .sharedContinuation
  | .doDup2Replace, false => some .sharedContinuation
  | .dup3InvalidFlags, true => some .noInstrumentation
  | .dup3Equal, true => some .noInstrumentation
  | .dup3TargetLimit, true => some .noInstrumentation
  | .dup3NoFile, true => some .noInstrumentation
  | .dup3ExpandError, false => some .compilerShared
  | .dup3ExpandEmfile, true => some .noInstrumentation
  | .dup3ExpandEmfile, false => some .sharedContinuation
  | .fgetRcuNoFile, true => some .noInstrumentation
  | .fgetRcuIncNotZeroFailed, true => some .noInstrumentation
  | .fgetRcuEntryChanged, true => some .sharedOperand
  | .fgetRcuEntryChanged, false => some .sharedOperand
  | .fgetRcuTableChanged, true => some .sharedOperand
  | .fgetRcuTableChanged, false => some .constantFolded
  | .fgetRcuMasked, false => some .constantFolded
  | .fgetLightNoFile, true => some .sharedOperand
  | .fgetLightNoFile, false => some .sharedOperand
  | .fgetLightMasked, true => some .sharedOperand
  | .fgetLightMasked, false => some .noInstrumentation
  | .fdgetPosHasFile, true => some .sharedOperand
  | .fdgetPosHasFile, false => some .sharedOperand
  | .fposLockAtomicPos, false => some .sharedContinuation
  | .fposLockShared, true => some .sharedOperand
  | .fposLockShared, false => some .sharedOperand
  | .fposLockIterateShared, true => some .sharedOperand
  | .fposLockIterateShared, false => some .sharedOperand
  | .fdputFput, false => some .sharedContinuation
  | .fdputPosUnlock, false => some .sharedContinuation
  | .dupFound, false => some .sharedContinuation
  | .anonGetfileOwner, true => some .constantFolded
  | .anonGetfileOwner, false => some .sharedContinuation
  | .anonMakeInode, true => some .constantFolded
  | .anonInodeErr, true => some .noInstrumentation
  | .anonInodeErr, false => some .sharedContinuation
  | .rwVerifyNegativeCount, true => some .noInstrumentation
  | .rwVerifyHasPos, false => some .sharedContinuation
  | .rwVerifyPosOverflow, false => some .sharedContinuation
  | .newSyncReadQueued, true => some .outsideDomain
  | .newSyncReadQueued, false => some .sharedContinuation
  | .vfsReadNotReadable, true => some .noInstrumentation
  | .vfsReadCannotRead, true => some .noInstrumentation
  | .vfsReadAccessFault, true => some .noInstrumentation
  | .vfsReadVerifyError, true => some .noInstrumentation
  | .vfsReadClamp, true => some .noInstrumentation
  | .vfsReadClamp, false => some .sharedContinuation
  | .vfsReadHasRead, true => some .compilerShared
  | .vfsReadHasReadIter, false => some .noInstrumentation
  | .vfsReadPositive, true => some .constantFolded
  | .vfsReadPositive, false => some .sharedContinuation
  | .filePposStream, true => some .branchFree
  | .filePposStream, false => some .branchFree
  | .ksysReadHasFile, false => some .sharedContinuation
  | .ksysReadHasPpos, false => some .sharedContinuation
  | .ksysReadRetNonneg, true => some .sharedOperand
  | .ksysReadRetNonneg, false => some .sharedOperand
  | .ksysReadStorePos, false => some .sharedContinuation
  | .fileStartWriteNotRegular, true => some .noInstrumentation
  | .fileEndWriteNotRegular, true => some .noInstrumentation
  | .vfsWriteNotWritable, true => some .noInstrumentation
  | .vfsWriteCannotWrite, true => some .noInstrumentation
  | .vfsWriteAccessFault, true => some .noInstrumentation
  | .vfsWriteVerifyError, true => some .noInstrumentation
  | .vfsWriteClamp, true => some .noInstrumentation
  | .vfsWriteClamp, false => some .sharedContinuation
  | .vfsWriteHasWriteIter, false => some .noInstrumentation
  | .vfsWritePositive, true => some .constantFolded
  | .vfsWritePositive, false => some .sharedContinuation
  | .ksysWriteHasFile, false => some .sharedContinuation
  | .ksysWriteHasPpos, false => some .sharedContinuation
  | .ksysWriteRetNonneg, true => some .sharedOperand
  | .ksysWriteRetNonneg, false => some .sharedOperand
  | .ksysWriteStorePos, false => some .sharedContinuation
  | .fcntlNoFile, true => some .noInstrumentation
  | .fcntlPathFile, false => some .sharedContinuation
  | .fcntlCaseGetfd, false => some .sharedContinuation
  | .fcntlCaseSetfd, false => some .sharedContinuation
  | .fcntlCaseGetfl, false => some .sharedContinuation
  | .fcntlGetfdSet, true => some .branchFree
  | .fcntlGetfdSet, false => some .branchFree
  | .doDup2NoTofree, true => some .inlineHelper
  | .allocFdtableOverNrOpen, false => some .sharedContinuation
  | .allocFdtableBelowWanted, true => some .noInstrumentation
  | .allocFdtableBelowWanted, false => some .sharedContinuation
  | .allocFdtableOverIntMax, true => some .noInstrumentation
  | .allocFdtableNoMem, true => some .noInstrumentation
  | .allocFdtableFdArrayNoMem, true => some .noInstrumentation
  | .allocFdtableBitmapNoMem, true => some .noInstrumentation
  | .copyFdtableShrink, true => some .outsideDomain
  | .expandFdtableShared, false => some .sharedContinuation
  | .expandFdtableBugNr, true => some .outsideDomain
  | .expandFdtableFreeOld, false => some .sharedContinuation
  | .fcntlCaseSetfl, false => some .sharedContinuation
  | .setflAppendChanged, true => some .sharedOperand
  | .setflAppendChanged, false => some .sharedOperand
  | .setflAppendOnly, true => some .noInstrumentation
  | .setflAppendOnly, false => some .sharedContinuation
  | .setflNoatimeRequested, true => some .sharedOperand
  | .setflNoatimeRequested, false => some .sharedOperand
  | .setflNoatimeNotSet, false => some .sharedContinuation
  | .setflNotOwnerOrCapable, true => some .noInstrumentation
  | .setflNotOwnerOrCapable, false => some .sharedContinuation
  | .setflNotFifo, true => some .sharedOperand
  | .setflNotFifo, false => some .sharedOperand
  | .setflDirect, true => some .sharedOperand
  | .setflDirect, false => some .sharedOperand
  | .setflCannotOdirect, true => some .noInstrumentation
  | .setflCannotOdirect, false => some .sharedContinuation
  | .setflHasCheckFlags, false => some .sharedContinuation
  | .setflError, true => some .noInstrumentation
  | .setflError, false => some .sharedContinuation
  | .setflFasyncChanged, true => some .sharedOperand
  | .setflFasyncChanged, false => some .sharedOperand
  | .setflHasFasync, false => some .sharedContinuation
  | .swapEndian128, false => some .sharedContinuation
  | .pushRcuNonNull, false => some .sharedContinuation
  | .rootRemoveLenPositive, true => some .sharedOperand
  | .rootRemoveLenPositive, false => some .sharedOperand
  | .rootRemovePopped, false => some .sharedContinuation
  | .rootRemoveHasPeer, false => some .sharedContinuation
  | .fls128High, true => some .branchFree
  | .fls128High, false => some .branchFree
  | .placementNode, true => some .sharedOperand
  | .placementNode, false => some .sharedOperand
  | .placementCidrLe, true => some .sharedOperand
  | .placementCidrLe, false => some .sharedOperand
  | .placementPrefixMatches, false => some .sharedContinuation
  | .addCidrTooLong, true => some .sharedOperand
  | .addCidrTooLong, false => some .sharedOperand
  | .addNoDown, false => some .sharedContinuation
  | .freeHasRoot4, false => some .sharedContinuation
  | .freeHasRoot6, false => some .sharedContinuation
  | .removeListIter, false => some .sharedContinuation
  | .removeHasBit0, true => some .sharedOperand
  | .removeHasBit0, false => some .sharedOperand
  | .removeHasBit1, false => some .sharedContinuation
  | .removeChildExists, false => some .sharedContinuation
  | .removeLeafBit0, false => some .sharedContinuation
  | .removeLeafBit1, false => some .sharedContinuation
  | .removeParentIsNode, false => some .sharedContinuation
  | .removeParentNoPeer, true => some .sharedContinuation
  | .removeParentNoPeer, false => some .sharedContinuation
  | .removeFreeParent, false => some .sharedContinuation
  | .removeSiblingExists, false => some .sharedContinuation
  | .readNodeHasCidr, false => some .sharedContinuation
  | .refcountAddNzRetry, true => some .sharedContinuation
  | .refcountAddNzRetry, false => some .sharedContinuation
  | .refcountAddNzNegative, true => some .sharedOperand
  | .refcountAddNzNegative, false => some .sharedOperand
  | .refcountAddNzWraps, true => some .sharedOperand
  | .refcountAddNzWraps, false => some .sharedContinuation
  | .refcountAddNegative, true => some .sharedOperand
  | .refcountAddNegative, false => some .sharedOperand
  | .refcountAddWraps, true => some .sharedOperand
  | .refcountAddWraps, false => some .sharedContinuation
  | .precomputeNoIdentity, true => some .sharedOperand
  | .precomputeNullPoint, true => some .sharedOperand
  | .precomputeNullPoint, false => some .sharedContinuation
  | .handshakeInitHasPsk, false => some .sharedContinuation
  | .expireNextKeypair, false => some .sharedContinuation
  | .expireCurrentKeypair, false => some .sharedContinuation
  | .peerGetMaybeZeroNull, true => some .sharedOperand
  | .peerGetMaybeZeroNull, false => some .sharedOperand
  | .peerGetMaybeZeroDead, true => some .sharedOperand
  | .peerRemoveNotDead, true => some .sameLine
  | .peerRemoveNotDead, false => some .sharedContinuation
  | .peerRemoveAllIter1, false => some .sharedContinuation
  | .peerRemoveAllIter2, false => some .sharedContinuation
  | .peerKrefPutReleased, false => some .sharedContinuation
  | .pubkeyLookupMatch, false => some .sharedContinuation
  | .eqA4, true => some .sharedOperand
  | .eqA4, false => some .sharedOperand
  | .eqB4, true => some .sharedOperand
  | .eqB4, false => some .sharedOperand
  | .eqPort4, true => some .sharedOperand
  | .eqPort4, false => some .sharedOperand
  | .eqAddr4, true => some .sharedOperand
  | .eqAddr4, false => some .sharedOperand
  | .eqSrc4, true => some .sharedOperand
  | .eqSrc4, false => some .sharedOperand
  | .eqSrcIf4, true => some .sharedOperand
  | .eqSrcIf4, false => some .sharedOperand
  | .eqA6, true => some .sharedOperand
  | .eqA6, false => some .sharedOperand
  | .eqB6, true => some .sharedOperand
  | .eqB6, false => some .sharedOperand
  | .eqPort6, true => some .sharedOperand
  | .eqPort6, false => some .sharedOperand
  | .eqAddr6, true => some .sharedOperand
  | .eqAddr6, false => some .sharedOperand
  | .eqScope6, true => some .sharedOperand
  | .eqScope6, false => some .sharedOperand
  | .eqSrc6, true => some .sharedOperand
  | .eqSrc6, false => some .sharedOperand
  | .eqANone, true => some .sharedOperand
  | .eqANone, false => some .sharedOperand
  | .eqBNone, true => some .sharedOperand
  | .eqBNone, false => some .sharedOperand
  | .lookupHasIfname, false => some .sharedContinuation
  | .lookupNoLinkOps, true => some .sharedOperand
  | .lookupNoLinkOps, false => some .sharedOperand
  | .lookupNoKind, true => some .sharedOperand
  | .lookupNoKind, false => some .sharedOperand
  | .getAipPutCidr, true => some .sharedOperand
  | .getAipPutFamily, true => some .sharedOperand
  | .getAipFamily6, true => some .branchFree
  | .getAipFamily6, false => some .branchFree
  | .getAipPutAddr, true => some .sharedOperand
  | .getPeerFirst, false => some .sharedContinuation
  | .getPeerPutHandshake, true => some .sharedOperand
  | .getPeerPutKeepalive, true => some .sharedOperand
  | .getPeerPutTx, true => some .sharedOperand
  | .getPeerPutRx, true => some .sharedOperand
  | .getPeerPutProto, true => some .sharedOperand
  | .getPeerEp6, false => some .sharedContinuation
  | .getPeerSeqChanged, false => some .sharedContinuation
  | .getPeerAipIter, false => some .sharedContinuation
  | .getPeerAipFail, false => some .sharedContinuation
  | .dumpFirst, false => some .sharedContinuation
  | .dumpPutPort, true => some .sharedOperand
  | .dumpPutFwmark, true => some .sharedOperand
  | .dumpPutIfindex, true => some .sharedOperand
  | .dumpPutIfname, true => some .sharedOperand
  | .dumpHasIdentity, false => some .sharedContinuation
  | .dumpPutPrivate, true => some .sharedOperand
  | .dumpPutPublic, true => some .sharedOperand
  | .dumpPutPublic, false => some .sharedContinuation
  | .dumpPeerListEmpty, true => some .sharedOperand
  | .dumpCursorSet, true => some .sharedOperand
  | .dumpCursorSet, false => some .sharedOperand
  | .dumpCursorDead, true => some .sharedOperand
  | .dumpCursorDead, false => some .sharedOperand
  | .dumpPeerIter, false => some .sharedContinuation
  | .dumpOutRetZero, true => some .sharedOperand
  | .dumpOutRetZero, false => some .sharedOperand
  | .dumpOutNotDone, true => some .sharedOperand
  | .dumpOutNotDone, false => some .sharedOperand
  | .dumpOutHasCursor, false => some .sharedContinuation
  | .getDoneHasWg, false => some .sharedContinuation
  | .setPortPeerIter, false => some .sharedContinuation
  | .aipNoFamily, true => some .sharedOperand
  | .aipNoFamily, false => some .sharedOperand
  | .aipNoAddr, true => some .sharedOperand
  | .aipNoAddr, false => some .sharedOperand
  | .aipNoCidr, true => some .sharedOperand
  | .aipV4Family, true => some .sharedOperand
  | .aipV4Family, false => some .sharedOperand
  | .aipV4Cidr, true => some .sharedOperand
  | .aipV4Cidr, false => some .sharedOperand
  | .aipV4Len, false => some .sharedContinuation
  | .aipV6Family, true => some .sharedOperand
  | .aipV6Family, false => some .sharedOperand
  | .aipV6Cidr, true => some .sharedOperand
  | .aipV6Cidr, false => some .sharedOperand
  | .aipV6Len, false => some .sharedContinuation
  | .peerHasPubkey, false => some .sharedContinuation
  | .peerPubkeyLen, false => some .sharedContinuation
  | .peerHasPsk, false => some .sharedContinuation
  | .peerPskLen, false => some .sharedContinuation
  | .peerHasFlags, false => some .sharedContinuation
  | .peerHasProtocol, false => some .sharedContinuation
  | .peerBadProtocol, false => some .sharedContinuation
  | .peerNotFound, false => some .sharedContinuation
  | .peerSelfHasIdentity, false => some .sharedContinuation
  | .peerSelfKeyMatch, false => some .sharedContinuation
  | .peerSetPsk, false => some .sharedContinuation
  | .peerHasEndpoint, false => some .sharedContinuation
  | .peerEndpointV4Len, true => some .sharedOperand
  | .peerEndpointV4Len, false => some .sharedOperand
  | .peerEndpointV4Family, false => some .sharedOperand
  | .peerEndpointV6Len, true => some .sharedOperand
  | .peerEndpointV6Len, false => some .sharedOperand
  | .peerEndpointV6Family, false => some .sharedContinuation
  | .peerReplaceAips, false => some .sharedContinuation
  | .peerHasAips, false => some .sharedContinuation
  | .peerAipsIter, false => some .sharedContinuation
  | .peerAipErr, false => some .sharedContinuation
  | .peerHasKeepalive, false => some .sharedContinuation
  | .peerKeepaliveWasZero, false => some .sharedContinuation
  | .peerKeepaliveNonzero, false => some .sharedContinuation
  | .peerKeepaliveRunning, true => some .sharedContinuation
  | .peerKeepaliveRunning, false => some .sharedContinuation
  | .peerSendKeepalive, false => some .sharedContinuation
  | .peerRunning, false => some .sharedContinuation
  | .peerZeroPsk, false => some .sharedContinuation
  | .setDevHasFlags, false => some .sharedContinuation
  | .setDevHasPort, true => some .sharedOperand
  | .setDevHasPort, false => some .sharedOperand
  | .setDevHasFwmark, true => some .sharedOperand
  | .setDevHasFwmark, false => some .sharedOperand
  | .setDevNoNet, true => some .sharedOperand
  | .setDevNoNet, false => some .sharedOperand
  | .setDevNotCapable, true => some .sharedOperand
  | .setDevNotCapable, false => some .sharedOperand
  | .setDevPermErr, false => some .sharedContinuation
  | .setDevFwmark, false => some .sharedContinuation
  | .setDevFwmarkPeerIter, false => some .sharedContinuation
  | .setDevPort, false => some .sharedContinuation
  | .setDevPortErr, false => some .sharedContinuation
  | .setDevReplacePeers, false => some .sharedContinuation
  | .setDevHasPrivateKey, false => some .sharedContinuation
  | .setDevPrivateKeyLen, false => some .sharedContinuation
  | .setDevGenPublic, false => some .sharedContinuation
  | .setDevOldPeer, false => some .sharedContinuation
  | .setDevSendStagedNoIdentity, true => some .sharedOperand
  | .setDevSendStagedNoIdentity, false => some .sharedOperand
  | .setDevSendStagedRunning, true => some .sharedOperand
  | .setDevSendStagedRunning, false => some .sharedOperand
  | .setDevSendStagedKept, true => some .sharedOperand
  | .setDevSendStagedKept, false => some .sharedOperand
  | .setDevSendStagedHasIdentity, true => some .sharedOperand
  | .setDevSendStagedHasIdentity, false => some .sharedOperand
  | .setDevKeyPeerIter, false => some .sharedContinuation
  | .setDevSendStagedPeer, false => some .sharedContinuation
  | .setDevHasPeers, false => some .sharedContinuation
  | .setDevPeersIter, false => some .sharedContinuation
  | .setDevSetPeerErr, false => some .sharedContinuation
  | .setDevZeroKey, false => some .sharedContinuation
  | .placementExact, true => some .noInstrumentation
  | .addRootNoMem, true => some .noInstrumentation
  | .addNewnodeNoMem, true => some .noInstrumentation
  | .removeListEmpty, true => some .noInstrumentation
  | .removeHasBit1, true => some .noInstrumentation
  | .removeParentIsNode, true => some .noInstrumentation
  | .removeNotFreeParent, true => some .noInstrumentation
  | .refcountAddNzZero, true => some .noInstrumentation
  | .genPublicNullSecret, true => some .noInstrumentation
  | .keypairPutNull, true => some .noInstrumentation
  | .peerCreateNoMem, true => some .noInstrumentation
  | .peerGetMaybeZeroDead, false => some .noInstrumentation
  | .peerRemoveNull, true => some .noInstrumentation
  | .peerPutNull, true => some .noInstrumentation
  | .peerKrefPutReleased, true => some .noInstrumentation
  | .pubkeyLookupMatch, true => some .noInstrumentation
  | .setEndpointEq, true => some .noInstrumentation
  | .setEndpointV6, false => some .noInstrumentation
  | .lookupBothOrNeither, true => some .noInstrumentation
  | .lookupNoDev, true => some .noInstrumentation
  | .getAipNoNest, true => some .noInstrumentation
  | .getPeerNoNest, true => some .noInstrumentation
  | .getPeerPubkeyFail, true => some .noInstrumentation
  | .getPeerEpFail, true => some .noInstrumentation
  | .getPeerNoAips, true => some .noInstrumentation
  | .getPeerSeqChanged, true => some .noInstrumentation
  | .getPeerAipsNestFail, true => some .noInstrumentation
  | .dumpNoHdr, true => some .noInstrumentation
  | .dumpNoPeersNest, true => some .noInstrumentation
  | .dumpNoPeersNest, false => some .noInstrumentation
  | .dumpGetPeerFail, true => some .noInstrumentation
  | .dumpGetPeerFail, false => some .noInstrumentation
  | .dumpDone, true => some .noInstrumentation
  | .setPortSame, true => some .noInstrumentation
  | .peerBadFlags, true => some .noInstrumentation
  | .peerBadProtocol, true => some .noInstrumentation
  | .peerNewRemoveOrUpdate, true => some .noInstrumentation
  | .peerCreateErr, true => some .noInstrumentation
  | .peerAipErr, true => some .noInstrumentation
  | .peerKeepaliveWasZero, true => some .noInstrumentation
  | .setDevBadFlags, true => some .noInstrumentation
  | .setDevPermErr, true => some .noInstrumentation
  | .setDevPortErr, true => some .noInstrumentation
  | .setDevSetPeerErr, true => some .noInstrumentation
  | .peerCreateMaxPeers, true => some .compilerShared
  | .addNoPeer, true => some .compilerShared
  | .dumpRetErr, false => some .compilerShared
  | .commonBits128, false => some .noInstrumentation
  | .dumpDone, false => some .compilerShared
  | .getPeerPskFail, true => some .compilerShared
  | .peerAipParseErr, true => some .compilerShared
  | .setDevParseErr, true => some .compilerShared
  | _, _ => none

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

/-- The decisions that are value comparisons. Exactly these report operands
    (`branchCmp`, as `(lhs, rhs)` in source order); the check requires it. -/
def Decision.comparison : Decision → Option Comparison
  | .allocFdCloexec => some ⟨.flag, true, none⟩
  | .placementCidrLe => some ⟨.le, false, none⟩
  | .placementExact => some ⟨.eq, false, none⟩
  | .addCidrTooLong => some ⟨.gt, false, none⟩
  | .peerCreateMaxPeers => some ⟨.ge, true, none⟩
  | .refcountAddFromZero => some ⟨.eq, true, none⟩
  | .refcountAddNzZero => some ⟨.eq, true, none⟩
  | .allocFdExpandError => some ⟨.lt, true, none⟩
  | .allocFdExpanded => some ⟨.ne, true, none⟩
  | .allocFdLimit => some ⟨.ge, false, none⟩
  | .allocFdSearch => some ⟨.lt, false, none⟩
  | .allocFdUpdateNextFd => some ⟨.le, false, none⟩
  | .closeFdOutOfRange => some ⟨.ge, false, none⟩
  | .ctxDoReadSemaphore => some ⟨.flag, true, none⟩
  | .doDup2Cloexec => some ⟨.flag, true, none⟩
  | .doEventfdFdError => some ⟨.lt, true, none⟩
  | .doEventfdInvalidFlags => some ⟨.flag, true, none⟩
  | .dup3Equal => some ⟨.eq, false, none⟩
  | .dup3ExpandError => some ⟨.lt, true, none⟩
  | .dup3InvalidFlags => some ⟨.flag, true, none⟩
  | .dup3TargetLimit => some ⟨.ge, false, none⟩
  | .dupAllocOk => some ⟨.ge, true, none⟩
  | .eventfdFreeCtxHasId => some ⟨.ge, true, none⟩
  | .eventfdReadEmpty => some ⟨.eq, true, none⟩
  | .eventfdReadNonblock => some ⟨.flag, true, none⟩
  | .eventfdReadShort => some ⟨.lt, true, none⟩
  | .eventfdWriteBlocking => some ⟨.flag, true, none⟩
  | .eventfdWriteFits => some ⟨.gt, false, none⟩
  | .eventfdWriteReserved => some ⟨.eq, true, none⟩
  | .eventfdWriteWrongSize => some ⟨.ne, true, none⟩
  | .expandFilesFits => some ⟨.lt, false, none⟩
  | .fcntlPathFile => some ⟨.flag, true, none⟩
  | .fdInstallBacking => some ⟨.flag, true, none⟩
  | .fgetLightSingleOwner => some ⟨.eq, true, none⟩
  | .fileFreeAccounted => some ⟨.flag, true, none⟩
  | .fileFreeBacking => some ⟨.flag, true, none⟩
  | .fileInitPathModeRead => some ⟨.flag, true, none⟩
  | .fileInitPathModeWrite => some ⟨.flag, true, none⟩
  | .fileInitPathReadOnly => some ⟨.eq, true, none⟩
  | .filePposStream => some ⟨.flag, true, none⟩
  | .filpFlushCountZero => some ⟨.eq, true, none⟩
  | .filpFlushNotPath => some ⟨.flag, true, none⟩
  | .findNextFdAllFull => some ⟨.ge, false, none⟩
  | .fposLockAtomicPos => some ⟨.flag, true, none⟩
  | .fputFinalFasync => some ⟨.flag, true, none⟩
  | .fputFinalNeedUnmount => some ⟨.flag, true, none⟩
  | .fputFinalNotOpened => some ⟨.flag, true, none⟩
  | .getFileFromZero => some ⟨.eq, true, none⟩
  | .iocbFlagsAppend => some ⟨.flag, true, none⟩
  | .iocbFlagsDirect => some ⟨.flag, true, none⟩
  | .iocbFlagsDsync => some ⟨.flag, true, none⟩
  | .iocbFlagsSync => some ⟨.flag, true, none⟩
  | .ksysReadRetNonneg => some ⟨.ge, true, none⟩
  | .ksysWriteRetNonneg => some ⟨.ge, true, none⟩
  | .putFileAccessReadOnly => some ⟨.eq, true, none⟩
  | .putFileAccessWriter => some ⟨.flag, true, none⟩
  | .putUnusedFdLowerNextFd => some ⟨.lt, false, none⟩
  | .refcountSubPositive => some ⟨.gt, true, none⟩
  | .refcountSubToZero => some ⟨.eq, true, none⟩
  | .rwVerifyNegativeCount => some ⟨.lt, true, none⟩
  | .vfsReadCannotRead => some ⟨.flag, true, none⟩
  | .vfsReadNotReadable => some ⟨.flag, true, none⟩
  | .vfsWriteCannotWrite => some ⟨.flag, true, none⟩
  | .vfsWriteNotWritable => some ⟨.flag, true, none⟩
  | .setflAppendChanged => some ⟨.flag, true, none⟩
  | .setflNoatimeRequested => some ⟨.flag, true, none⟩
  | .setflNoatimeNotSet => some ⟨.flag, true, none⟩
  -- the three-line condition at fcntl.c:62-64: DWARF attributes `arg & O_DIRECT`
  -- to 62 and `f_mode & FMODE_CAN_ODIRECT` to 63, one line before their source
  | .setflDirect => some ⟨.flag, true, some 62⟩
  | .setflCannotOdirect => some ⟨.flag, true, some 63⟩
  | .setflFasyncChanged => some ⟨.flag, true, none⟩
  | .allocFdtableOverNrOpen => some ⟨.gt, false, none⟩
  | .expandFilesOverNrOpen => some ⟨.ge, false, none⟩
  | .setflAppendOnly => some ⟨.flag, true, none⟩
  | .setflNotOwnerOrCapable => some ⟨.eq, true, none⟩
  | .setflNotFifo => some ⟨.ne, true, none⟩
  | .allocFdtableBelowWanted => some ⟨.lt, false, none⟩
  | .allocFdtableOverIntMax => some ⟨.gt, true, none⟩
  | .copyFdtableShrink => some ⟨.lt, false, none⟩
  | .expandFdtableShared => some ⟨.gt, true, none⟩
  | .expandFdtableBugNr => some ⟨.lt, false, none⟩
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
  | .refcountSubToZero | .refcountSubNonpositive | .refcountSubUnderflow => true
  | _ => false

/-- Every decision, enumerated through the constructor index. -/
def Decision.all : List Decision :=
  (List.range 4096).filterMap fun i =>
    let x := Decision.ofNat i
    if x.ctorIdx == i then some x else none

def Step.label (s : Step) : String :=
  s!"{s.decision.info.label}={if s.outcome then 1 else 0}"

end Leanux
