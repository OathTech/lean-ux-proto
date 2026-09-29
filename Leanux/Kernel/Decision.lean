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
  | fcntlNoFile | fcntlPathFile | fcntlCaseGetfd | fcntlCaseSetfd | fcntlCaseGetfl | fcntlGetfdSet
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A recorded step: the decision and the outcome the mirror computed. -/
structure Step where
  decision : Decision
  outcome : Bool
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
  | _, _ => none

/-- Every decision, enumerated through the constructor index. -/
def Decision.all : List Decision :=
  (List.range 4096).filterMap fun i =>
    let x := Decision.ofNat i
    if x.ctorIdx == i then some x else none

def Step.label (s : Step) : String :=
  s!"{s.decision.info.label}={if s.outcome then 1 else 0}"

end Leanux
