import Leanux.FS.File
import Leanux.FS.AnonInodes

/-!
# fs/eventpoll.c — the epoll mirror (tier 1)

Design: docs/2026-10-12-epoll-design.md (v2), sections 2 and 4. One Lean
function per C function, same names, the decisions in the C's order. Line
numbers are the pristine source's (`.deps/linux`): the check reads statements
and spans there, so the kind-308 hook, like every patch of an anchored file,
keeps the file's line count. Tier 1 is `timeout 0` with a single task: a blocking
wait, a pending signal, `POLLFREE`, a target that is neither an eventfd, a
pipe end nor an epoll file stop `unsupported`; the arms a single task cannot
reach (`dying`, a failed `epi_fget`, a callback during a scan, the seqcount
retry, the first-ADD arm of `loop_check_gen`) stop `invariant`.

Cuts, each named at its helper: the rbtree (`epFind`, `epRbtreeInsert`,
design 3.2); `kfree_rcu` and the slab frees (no retained state); the mutexes,
spinlocks and RCU sections (one task); `cond_resched` in a system call (no
dispatch section is open, so the kernel records nothing: `__cond_resched`
schedules nothing the mirror runs); `free_uid` (kernel/user.c, unanchored);
the empty `__pm_*` helpers of a kernel without `CONFIG_PM`.

The wake callback (`ep_poll_callback`) and `ep_poll_safewake` live in
`Leanux.FS.Wait` with the walk they recurse through, and the queue
registration (`ep_ptable_queue_proc`) in `Leanux.FS.Poll` with `poll_wait`:
the module order follows the C's call graph, which has those cycles.
-/

namespace Leanux

/-! ## Constants (fs/eventpoll.c:212-226, include/uapi/linux/eventpoll.h) -/

def EPOLL_CLOEXEC : UInt32 := O_CLOEXEC
def EPOLL_CTL_ADD : Int := 1
def EPOLL_CTL_DEL : Int := 2
def EPOLL_CTL_MOD : Int := 3
/-- `EPOLLEXCLUSIVE_OK_BITS` (:215-216). -/
def EPOLLEXCLUSIVE_OK_BITS : UInt32 :=
  EPOLLINOUT_BITS ||| EPOLLERR ||| EPOLLHUP ||| EPOLLWAKEUP ||| EPOLLET ||| EPOLLEXCLUSIVE
/-- `EP_MAX_EVENTS = INT_MAX / sizeof(struct epoll_event)` (:221), 12 bytes packed. -/
def EP_MAX_EVENTS : Int := 2147483647 / 12
/-- `path_limits` (:1602). -/
def PATH_LIMITS : Array Nat := #[1000, 500, 100, 50, 10]
/-- `ELOOP`, `ENOSPC`, `ENOENT`, `EINTR`. -/
def ELOOP : Int := 40
def ENOSPC : Int := 28
def ENOENT : Int := 2
def EINTR : Int := 4

/-- `struct epoll_event` (include/uapi/linux/eventpoll.h:80-83). -/
structure EpollEvent where
  events : UInt32
  data : UInt64
  deriving Repr, BEq

/-- `is_file_epoll(f)` (:493-496): `f->f_op == &eventpoll_fops`, a pointer
    compare the mirror holds as the fops identity. -/
def isFileEpoll (f : File) : Bool := f.fOp == some .eventpoll

/-- `file->private_data` of an epoll file. -/
def epOf (f : File) : M EpId :=
  match f.privateData with
  | some (.eventpoll e) => return e
  | _ => invariant "an epoll operation on a file whose private_data is not an eventpoll"

/-- The `epitems` list a file's `f_ep` heads: a non-epoll file's head, or an
    epoll file's `ep->refs` (both `hlist`, head first). -/
def fEpItems (f : File) : M (List EpiId) :=
  match f.fEp with
  | .null => return []
  | .head items => return items
  | .epRefs e => return (← getEp e).refs

/-- `hlist_del_rcu(&epi->fllink)` from the list `file->f_ep` heads; after
    `ep_remove_file` nulled `f_ep` the node was the list's only one. -/
def fEpUnlink (fid : FileId) (epi : EpiId) : M Unit := do
  let f ← getFile fid
  match f.fEp with
  | .null => pure ()
  | .head items => setFile fid { f with fEp := .head (items.erase epi) }
  | .epRefs e => setEp e { (← getEp e) with refs := (← getEp e).refs.erase epi }

/-- `atomic_long_inc_not_zero(&file->f_count)` (`raw_atomic64_fetch_add_unless`):
    with one task the cmpxchg succeeds at once, so the outcome is `f_count != 0`,
    and the count is incremented iff it was non-zero. The caller records the
    decision at its own line, as `__fget_files_rcu`'s does. -/
def fileIncNotZero (fid : FileId) : M Bool := do
  let f ← getFile fid
  if f.fCount == 0 then return false
  setFile fid { f with fCount := f.fCount + 1 }
  return true

/-! ## tfile_check_list (:419-462, :2385-2393) -/

/-- `free_ephead(head)` (:419-423): `kmem_cache_free` is a cut; the head's
    identity is its file's `f_ep`, so nothing is retained. -/
def freeEphead (head : Bool) : M Unit := do
  if ← branch .freeEpheadNonNull head then pure ()   -- kmem_cache_free(ephead_cache, head)

/-- `list_file(file)` (:425-444): the head of a non-epoll file that an
    item links joins `tfile_check_list` with a reference to the file, unless
    it is listed already (`head->next` non-NULL). -/
def listFile (fid : FileId) : M Unit := do
  -- head = container_of(file->f_ep, struct epitems_head, epitems)
  if ← branch .listFileUnlisted (!(← getK).tfileCheckList.contains fid) then
    if ← branch .listFileIncNotZeroFailed (!(← fileIncNotZero fid)) then return   -- a dying leaf
    -- head->file = file; head->next = tfile_check_list; tfile_check_list = head
    modifyK fun k => { k with tfileCheckList := fid :: k.tfileCheckList }

/-- `unlist_file(head)` (:446-462): the head is freed unless items still
    hang on it; the reference `list_file` took is dropped. A head whose
    file's `f_ep` was nulled by `ep_remove_file` has no items. -/
def unlistFile (fid : FileId) : M Unit := do
  -- to_free = head; p = hlist_first_rcu(&head->epitems); file = head->file
  let items ← fEpItems (← getFile fid)
  let mut toFree := true
  if ← branch .unlistFileHasItem (!items.isEmpty) then
    -- spin_lock(&epi->ffd.file->f_lock)
    if ← branch .unlistFileItemsRemain (!items.isEmpty) then toFree := false
    -- head->next = NULL; head->file = NULL; spin_unlock
  freeEphead toFree
  fput fid

/-- `clear_tfile_check_list()` (:2385-2393). -/
def clearTfileCheckList : M Unit := do
  -- rcu_read_lock()
  for _ in [0:4096] do
    match (← getK).tfileCheckList with
    | [] => break
    | fid :: rest =>
      _ ← branch .clearTfileCheckListIter true
      -- head = tfile_check_list; tfile_check_list = head->next
      modifyK fun k => { k with tfileCheckList := rest }
      unlistFile fid
  _ ← branch .clearTfileCheckListIter false
  -- rcu_read_unlock()

/-! ## The tree (:1357-1378, :1568-1586): the ordered-map cut (design 3.2)

`ep_find` and `ep_rbtree_insert` walk a red-black tree keyed by
`ep_cmp_ffd` (:507-512): the `struct file` address first, the fd second. The
walks and `lib/rbtree.c`'s rebalancing are a cut: inputs the key, result the
item or its absence, no retained state beyond the map, and the callers'
`rb_first`/`rb_next` iterations follow the key order the kind-308 record
fixes. The `kcmp` comparisons inside are not mirror decisions (the tree's
shape is the rebalancing's); both functions are inlined into `do_epoll_ctl`
and `ep_register_epitem`, listed in `correspondence/kcov.json`. -/

/-- `ep_find(ep, file, fd)` (:1357-1378): equality of `ep_cmp_ffd` is the
    same file and the same fd. -/
def epFind (ep : EpId) (fid : FileId) (fd : Int) : M (Option EpiId) := do
  -- ep_set_ffd(&ffd, file, fd); the walk
  for (_, epiId) in (← getEp ep).rbr do
    let epi ← getEpi epiId
    if epi.file == fid && epi.fd == fd then return some epiId
  return none

/-- `ep_rbtree_insert(ep, epi)` (:1568-1586): the item's key is
    `(ffd.file, ffd.fd)`; the file address is the kind-308 record the hook
    at :1586 writes once per call. A file's address is stable for its
    lifetime: an item of the same file with another recorded address is a
    hidden mismatch. -/
def epRbtreeInsert (ep : EpId) (epiId : EpiId) : M Unit := do
  let epi ← getEpi epiId
  let addr ← hiddenU64 .epollInsertAddress
  -- a placeholder (the domain filter, before Linux) carries no address
  if (← get).hidden.isSome && (← getK).epis.any (fun _ e => e.file == epi.file && e.fileAddr != 0 && e.fileAddr != addr) then
    throw (.hidden s!"ep_rbtree_insert: file {epi.file} recorded at address {addr}, before at another")
  setEpi epiId { epi with fileAddr := addr }
  let key := (addr, epi.fd)
  let e ← getEp ep
  let rec place : List ((Nat × Int) × EpiId) → List ((Nat × Int) × EpiId)
    | [] => [(key, epiId)]
    | (k, i) :: rest =>
      if key.1 < k.1 || (key.1 == k.1 && key.2 < k.2) then (key, epiId) :: (k, i) :: rest
      else (k, i) :: place rest
  setEp ep { e with rbr := place e.rbr }
  -- rb_insert_color_cached(&epi->rbn, &ep->rbr, leftmost): lib/rbtree.c, the cut

/-! ## Reverse paths (:1590-1669) -/

/-- `path_count_inc(nests)` (:1606-1614). -/
def pathCountInc (nests : Nat) : M Int := do
  if ← branchCmp .pathCountIncDepthZero (nests == 0) nests 0 then return 0
  let count := (← getK).pathCount[nests]! + 1
  modifyK fun k => { k with pathCount := k.pathCount.set! nests count }
  if ← branchCmp .pathCountIncOverLimit (count > PATH_LIMITS[nests]!) count PATH_LIMITS[nests]! then return -1
  return 0

/-- `reverse_path_check_proc(refs, depth)` (:1625-1643): a chain is counted
    at the set that no set watches, else the walk recurses into its
    watchers. The depth arm is bounded by the loop check (design 2.7). The
    recursion is through `refs`, at most `EP_MAX_NESTS + 1` deep. -/
def reversePathCheckProc : Nat → List EpiId → Nat → M Int
  | 0, _, _ => invariant "reverse_path_check_proc nested beyond EP_MAX_NESTS + 2"
  | fuel + 1, refs, depth => do
    if ← branchCmp .reversePathCheckProcTooDeep (depth > EP_MAX_NESTS) depth EP_MAX_NESTS then
      invariant "reverse_path_check_proc deeper than EP_MAX_NESTS (the loop check bounds it)"
    let mut error : Int := 0
    for epiId in refs do
      _ ← branch .reversePathCheckProcIter true
      let setRefs := (← getEp (← getEpi epiId).ep).refs
      error ← if ← branch .reversePathCheckProcUnwatched setRefs.isEmpty then pathCountInc depth
              else reversePathCheckProc fuel setRefs (depth + 1)
      if ← branch .reversePathCheckProcError (error != 0) then return error
    _ ← branch .reversePathCheckProcIter false
    return error

/-- `reverse_path_check()` (:1656-1669): from each listed file. -/
def reversePathCheck : M Int := do
  for fid in (← getK).tfileCheckList do
    _ ← branch .reversePathCheckListIter true
    modifyK fun k => { k with pathCount := #[0, 0, 0, 0, 0] }   -- path_count_init()
    -- rcu_read_lock()
    let error ← reversePathCheckProc (EP_MAX_NESTS + 2) (← fEpItems (← getFile fid)) 0
    -- rcu_read_unlock()
    if ← branchCmp .reversePathCheckError (error != 0) error 0 then return error
  _ ← branch .reversePathCheckListIter false
  return 0

/-! ## Scans (:893-962) -/

/-- `ep_start_scan(ep, &scan_batch)` (:893-912): the ready list moves to
    the caller's batch (its items stay `linked`: `rdllink` is on the batch)
    and the set enters scanning. Returns the batch. -/
def epStartScan (ep : EpId) : M (List EpiId) := do
  -- spin_lock_irq(&ep->lock); write_seqcount_begin(&ep->seq)
  let e ← getEp ep
  let batch := e.rdllist
  -- list_splice_init(&ep->rdllist, scan_batch); ep_enter_scan(ep)
  -- write_seqcount_end(&ep->seq); spin_unlock_irq
  setEp ep { e with rdllist := [], ovflist := some [], seq := e.seq + 2 }
  return batch

/-- `ep_done_scan(ep, &scan_batch)` (:916-962): the overflow chain
    (LIFO) is head-inserted, which makes it FIFO, then the batch's
    leftovers are spliced at the head. -/
def epDoneScan (ep : EpId) (batch : List EpiId) : M Unit := do
  -- spin_lock_irq(&ep->lock)
  let chain := (← getEp ep).ovflist.getD []
  for epiId in chain do
    _ ← branch .epDoneScanOvflistIter true
    let epi ← getEpi epiId
    setEpi epiId { epi with onOvflist := false }   -- epi_clear_ovflist(epi)
    if ← branch .epDoneScanNotLinked (!epi.linked) then
      -- list_add(&epi->rdllink, &ep->rdllist); ep_pm_stay_awake (empty)
      let e ← getEp ep
      setEp ep { e with rdllist := epiId :: e.rdllist }
      setEpi epiId { (← getEpi epiId) with linked := true }
  _ ← branch .epDoneScanOvflistIter false
  -- write_seqcount_begin; ep_exit_scan(ep); list_splice(scan_batch, &ep->rdllist); write_seqcount_end
  let e ← getEp ep
  setEp ep { e with ovflist := none, rdllist := batch ++ e.rdllist, seq := e.seq + 2 }
  -- __pm_relax(ep->ws): empty without CONFIG_PM
  if ← branch .epDoneScanRdllistNonEmpty (!(← getEp ep).rdllist.isEmpty) then
    if ← branch .epDoneScanWqActive (← waitqueueActive (.epWq ep)) then
      unsupported "wake_up(&ep->wq) at ep_done_scan: a task sleeping in epoll_wait (tier 2)"
  -- spin_unlock_irq(&ep->lock)

/-! ## Reference counts (:964-988) -/

/-- `ep_get(ep)` (:964-967): `refcount_inc(&ep->refcount)`. -/
def epGet (ep : EpId) : M Unit := do
  let e ← getEp ep
  refcountInc e.refcount
  setEp ep { e with refcount := e.refcount + 1 }

/-- `ep_refcount_dec_and_test(ep)` (:972-979). -/
def epRefcountDecAndTest (ep : EpId) : M Bool := do
  let e ← getEp ep
  let zero ← refcountDecAndTest e.refcount
  setEp ep { e with refcount := e.refcount - 1 }
  if ← branch .epRefcountDecAndTestNotZero (!zero) then return false
  -- WARN_ON_ONCE(!RB_EMPTY_ROOT(&ep->rbr.rb_root))
  if ← branch .epRefcountDecAndTestTreeNotEmpty (!e.rbr.isEmpty) then
    invariant "an eventpoll disposed with items in its tree"
  return true

/-- `ep_free(ep)` (:981-988): `mutex_destroy`, `free_uid(ep->user)` (the
    root user's count, kernel/user.c, a cut), `wakeup_source_unregister(NULL)`
    and `kfree_rcu`. -/
def epFree (ep : EpId) : M Unit := freeEp ep

/-! ## Removal (:822-854, :1007-1100) -/

/-- `ep_remove_wait_queue(pwq)` (:822-838). -/
def epRemoveWaitQueue (pwqId : PwqId) : M Unit := do
  -- rcu_read_lock(); whead = smp_load_acquire(&pwq->whead)
  let pwq ← getPwq pwqId
  if ← branch .epRemoveWaitQueueWhead pwq.whead.isSome then
    if let some whead := pwq.whead then removeWaitQueue whead { func := .epPollCallback pwqId }
  -- rcu_read_unlock()

/-- `ep_unregister_pollwait(ep, epi)` (:843-854), with `mtx` held. -/
def epUnregisterPollwait (_ep : EpId) (epiId : EpiId) : M Unit := do
  for _ in [0:4096] do
    match (← getEpi epiId).pwqlist with
    | [] => break
    | pwqId :: rest =>
      _ ← branch .epUnregisterPollwaitNext true
      -- *p = pwq->next
      setEpi epiId { (← getEpi epiId) with pwqlist := rest }
      epRemoveWaitQueue pwqId
      freePwq pwqId   -- kmem_cache_free(pwq_cache, pwq)
  _ ← branch .epUnregisterPollwaitNext false

/-- `ep_remove_file(ep, epi, file)` (:1021-1044), with `file->f_lock` held;
    returns with it released. -/
def epRemoveFile (_ep : EpId) (epiId : EpiId) (fid : FileId) : M Unit := do
  let file ← getFile fid
  let items ← fEpItems file
  let mut toFree := false
  if ← branch .epRemoveFileSingular (items == [epiId]) then
    -- WRITE_ONCE(file->f_ep, NULL)
    setFile fid { file with fEp := .null }
    if let .epRefs e := file.fEp then setEp e { (← getEp e) with refs := [] }
    if ← branch .epRemoveFileNotEpoll (!isFileEpoll file) then
      -- v = container_of(head, ...); `!smp_load_acquire(&v->next)`: not on tfile_check_list
      if ← branch .epRemoveFileHeadUnlisted (!(← getK).tfileCheckList.contains fid) then toFree := true
  -- hlist_del_rcu(&epi->fllink)
  fEpUnlink fid epiId
  -- spin_unlock(&file->f_lock)
  freeEphead toFree

/-- `ep_remove_epi(ep, epi)` (:1046-1069): the tree, the ready list, the
    item's memory (`kfree_rcu`) and the user's watch count; always true. -/
def epRemoveEpi (ep : EpId) (epiId : EpiId) : M Bool := do
  -- rb_erase_cached(&epi->rbn, &ep->rbr): the ordered-map cut
  let e ← getEp ep
  setEp ep { e with rbr := e.rbr.filter (·.2 != epiId) }
  -- spin_lock_irq(&ep->lock)
  let epi ← getEpi epiId
  if ← branch .epRemoveEpiLinked epi.linked then
    -- list_del_init(&epi->rdllink)
    let e ← getEp ep
    setEp ep { e with rdllist := e.rdllist.erase epiId }
  -- spin_unlock_irq; wakeup_source_unregister(NULL); kfree_rcu(epi, rcu)
  freeEpi epiId
  -- percpu_counter_dec(&ep->user->epoll_watches)
  modifyK fun k => { k with user := { k.user with epollWatches := k.user.epollWatches - 1 } }
  return true

/-- `ep_remove(ep, epi)` (:1074-1100), for callers owning a reference to the
    set. The scoped `__free(fput)` drops `epi_fget`'s reference at the
    return; its `if (_T)` test is the cleanup's, on the live path non-NULL. -/
def epRemove (ep : EpId) (epiId : EpiId) : M Unit := do
  -- struct file *file __free(fput) = NULL
  epUnregisterPollwait ep epiId
  let epi ← getEpi epiId
  if ← branch .epRemoveDying epi.dying then
    invariant "ep_remove of a dying item (a concurrent eventpoll_release_file)"
  -- file = epi_fget(epi)
  let got ← fileIncNotZero epi.file
  _ ← branch .epiFgetIncNotZeroFailed (!got)
  if ← branch .epRemoveNoFile (!got) then
    invariant "epi_fget failed at ep_remove: the item's file has no reference"
  -- spin_lock(&file->f_lock)
  epRemoveFile ep epiId epi.file
  if ← branch .epRemoveRemoved (← epRemoveEpi ep epiId) then
    -- WARN_ON_ONCE(ep_refcount_dec_and_test(ep))
    if ← branch .epRemoveRefcountZero (← epRefcountDecAndTest ep) then
      invariant "the set's count reached zero at ep_remove (its file holds a reference)"
  _ ← branch .epRemoveFreeFile true
  fput epi.file

/-- `ep_clear_and_put(ep)` (:1101-1141): two whole-tree walks in key order,
    all unregistrations first, then all removals; then the set's own
    reference. The `cond_resched` of each walk runs in a system call with
    no dispatch section open: nothing is recorded or run. -/
def epClearAndPut (ep : EpId) : M Unit := do
  if ← branch .epClearAndPutPollWaitActive (← waitqueueActive (.epPollWait ep)) then
    invariant "an active poll_wait at ep_clear_and_put (eventpoll_release unhooks every watcher first)"
  -- mutex_lock(&ep->mtx)
  for (_, epiId) in (← getEp ep).rbr do
    _ ← branch .epClearAndPutUnregisterIter true
    epUnregisterPollwait ep epiId
    -- cond_resched()
  _ ← branch .epClearAndPutUnregisterIter false
  for (_, epiId) in (← getEp ep).rbr do   -- next = rb_next(rbp) before each removal
    _ ← branch .epClearAndPutRemoveIter true
    epRemove ep epiId
    -- cond_resched()
  _ ← branch .epClearAndPutRemoveIter false
  -- mutex_unlock(&ep->mtx)
  if ← branch .epClearAndPutLast (← epRefcountDecAndTest ep) then epFree ep

/-- `ep_eventpoll_release(inode, file)` (:1165-1172), the `release` operation. -/
def epEventpollRelease (fid : FileId) : M Int := do
  let ep ← epOf (← getFile fid)
  if ← branch .epEventpollReleaseHasEp true then epClearAndPut ep
  return 0

/-- `eventpoll_release_file(file)` (:1287-1325), from `__fput` through
    `eventpoll_release` (include/linux/eventpoll.h:34-54): each item on
    the file, in list order, is marked dying, unregistered, unlinked and
    removed. The set's count cannot reach zero here (its file holds a
    reference). -/
def eventpollReleaseFile (fid : FileId) : M Unit := do
  for _ in [0:4096] do   -- again:
    -- spin_lock(&file->f_lock)
    let file ← getFile fid
    let items ← fEpItems file
    let hasItem ← do
      if ← branch .eventpollReleaseFileHasFEp (file.fEp != .null) then
        branch .eventpollReleaseFileHasItem (!items.isEmpty)
      else pure false
    if !hasItem then break
    let epiId := items.head!
    setEpi epiId { (← getEpi epiId) with dying := true }   -- WRITE_ONCE(epi->dying, true)
    -- spin_unlock(&file->f_lock); ep = epi->ep; mutex_lock(&ep->mtx)
    let ep := (← getEpi epiId).ep
    epUnregisterPollwait ep epiId
    -- spin_lock(&file->f_lock)
    epRemoveFile ep epiId fid
    let dispose ← epRemoveEpi ep epiId
    -- mutex_unlock(&ep->mtx)
    if ← branch .eventpollReleaseFileDispose dispose then
      if ← branch .eventpollReleaseFileLast (← epRefcountDecAndTest ep) then
        invariant "the set's count reached zero at eventpoll_release_file (its file holds a reference)"
    -- goto again
  -- spin_unlock(&file->f_lock)

/-! ## Polling (:1175-1244) -/

/-- `ep_set_busy_poll_napi_id(epi)` (:656-685): returns at
    `ep_busy_loop_on` (:610-613), both terms zero in the fixture (design 3.3). -/
def epSetBusyPollNapiId (epiId : EpiId) : M Unit := do
  let e ← getEp (← getEpi epiId).ep
  _ ← branchCmp .epBusyLoopOnUsecs (e.busyPollUsecs != 0) e.busyPollUsecs 0
  _ ← branch .epBusyLoopOnNet false   -- net_busy_loop_on(): sysctl_net_busy_poll is 0
  _ ← branch .epSetBusyPollNotOn true

mutual

/-- `ep_item_poll(epi, pt, depth)` (:1220-1239): the file's `poll` with
    `pt->_key = epi->event.events`, the result masked by the interest. -/
def epItemPoll (fuel : Nat) (epiId : EpiId) (pt : PollTable) (depth : Nat) : M UInt32 := do
  let epi ← getEpi epiId
  -- file = epi_fget(epi)
  let got ← fileIncNotZero epi.file
  _ ← branch .epiFgetIncNotZeroFailed (!got)
  if ← branch .epItemPollNoFile (!got) then
    invariant "epi_fget failed at ep_item_poll: the item's file has no reference"
  let pt := { pt with key := epi.events }   -- pt->_key = epi->event.events
  let file ← getFile epi.file
  let res ← if ← branch .epItemPollNotEpoll (!isFileEpoll file) then vfsPoll epi.file pt
            else match fuel with
              | 0 => invariant "ep_item_poll nested beyond EP_MAX_NESTS + 2"
              | fuel + 1 => epEventpollPollInner fuel epi.file pt depth
  fput epi.file
  return res &&& epi.events
termination_by (fuel, 0)

/-- `__ep_eventpoll_poll(file, wait, depth)` (:1175-1212), an epoll file's
    `poll`: registers on its `poll_wait`, then scans its ready list, polling
    each item at `depth + 1`; the first ready item ends the scan with
    `EPOLLIN | EPOLLRDNORM`, an item found not ready leaves the list. -/
def epEventpollPollInner (fuel : Nat) (fid : FileId) (wait : PollTable) (depth : Nat) : M UInt32 := do
  let ep ← epOf (← getFile fid)
  let pt : PollTable := {}   -- init_poll_funcptr(&pt, NULL)
  pollWait fid (.epPollWait ep) wait
  -- mutex_lock_nested(&ep->mtx, depth)
  let batch ← epStartScan ep
  let mut res : UInt32 := 0
  let mut remaining := batch
  let mut broke := false
  for epiId in batch do
    _ ← branch .epEventpollPollIter true
    let r ← epItemPoll fuel epiId pt (depth + 1)
    if ← branchCmp .epEventpollPollReady (r != 0) r.toNat 0 then
      res := EPOLLIN ||| EPOLLRDNORM
      broke := true
      break
    -- __pm_relax(ep_wakeup_source(epi)) (empty); list_del_init(&epi->rdllink)
    remaining := remaining.erase epiId
    setEpi epiId { (← getEpi epiId) with linked := false }
  if !broke then _ ← branch .epEventpollPollIter false
  epDoneScan ep remaining
  -- mutex_unlock(&ep->mtx)
  return res
termination_by (fuel, 1)

end

/-- `ep_item_poll` from the slice's call sites, with the nesting budget. -/
def epItemPollAt (epiId : EpiId) (pt : PollTable) (depth : Nat) : M UInt32 :=
  epItemPoll (EP_MAX_NESTS + 2) epiId pt depth

/-! ## Creation (:1327-1349, :2398-2439) -/

/-- `ep_alloc(&ep)` (:1327-1349). `get_current_user()` increments the root
    user's count, a guest-wide value (the operand exclusion of fs/pipe.c:794,
    here at :1343). -/
def epAlloc : M (Except Int EpId) := do
  if ← branch .epAllocNoMem (!(← hiddenAlloc .kzallocEp)) then return .error (-ENOMEM)
  -- mutex_init, spin_lock_init, seqcount_spinlock_init, init_waitqueue_head x2,
  -- INIT_LIST_HEAD(&ep->rdllist), ep->rbr = RB_ROOT_CACHED, ep->ovflist = EP_UNACTIVE_PTR
  refcountIncGuestWide .rootUserCount   -- ep->user = get_current_user()
  -- refcount_set(&ep->refcount, 1)
  let id := (← getK).nextEp
  setEp id {}
  modifyK fun k => { k with nextEp := id + 1 }
  return .ok id

/-- `do_epoll_create(flags)` (:2398-2439). -/
def doEpollCreate (flags : UInt32) : M Int := do
  if ← branchCmp .doEpollCreateInvalidFlags (flags &&& ~~~EPOLL_CLOEXEC != 0) (flags &&& ~~~EPOLL_CLOEXEC).toNat 0 then
    return -EINVAL
  let r ← epAlloc
  if ← branch .doEpollCreateAllocError (r matches .error _) then
    return match r with | .error e => e | .ok _ => 0
  let .ok ep := r | invariant "unreachable"
  let fd ← getUnusedFdFlags (O_RDWR ||| (flags &&& O_CLOEXEC))
  if ← branchCmp .doEpollCreateFdError (fd < 0) fd 0 then
    epClearAndPut ep   -- out_free_ep
    return fd
  let file ← anonInodeGetfile .eventpoll (.eventpoll ep) (O_RDWR ||| (flags &&& O_CLOEXEC))
  if ← branch .doEpollCreateFileError (file matches .error _) then
    putUnusedFd fd.toNat   -- out_free_fd
    epClearAndPut ep       -- out_free_ep
    return match file with | .error e => e | .ok _ => 0
  let .ok fid := file | invariant "unreachable"
  setEp ep { (← getEp ep) with file := some fid }   -- ep->file = file
  fdInstall fd.toNat fid
  return fd

/-! ## Insertion and modification (:1707-1980) -/

/-- `ep_attach_file(file, epi)` (:1709-1741): the item joins the head of
    the target's `f_ep` list, a fresh `epitems_head` for a non-epoll file
    without one, an epoll file's own `refs`. -/
def epAttachFile (fid : FileId) (epiId : EpiId) : M Int := do
  let file ← getFile fid
  let ep ← if ← branch .epAttachFileIsEpoll (isFileEpoll file) then some <$> epOf file else pure none
  let mut head : Option FEp := none
  let mut toFree := false
  if ← branch .epAttachFileEp ep.isSome then
    head := some (.epRefs ep.get!)
  else if ← branch .epAttachFileNoFEp (file.fEp == .null) then
    -- allocate: to_free = kmem_cache_zalloc(ephead_cache, GFP_KERNEL)
    if ← branch .epAttachFileHeadNoMem (!(← hiddenAlloc .kmemCacheZallocEphead)) then return -ENOMEM
    toFree := true
    head := some (.head [])
  -- spin_lock(&file->f_lock)
  let file ← getFile fid
  if ← branch .epAttachFileFEpNull (file.fEp == .null) then
    match head with
    | none =>
      _ ← branch .epAttachFileRace true
      invariant "ep_attach_file: f_ep NULL under the lock with no head (a concurrent attach)"
    | some h =>
      _ ← branch .epAttachFileRace false
      setFile fid { file with fEp := h }   -- WRITE_ONCE(file->f_ep, head)
      toFree := false
  -- hlist_add_head_rcu(&epi->fllink, file->f_ep)
  let file ← getFile fid
  match file.fEp with
  | .head items => setFile fid { file with fEp := .head (epiId :: items) }
  | .epRefs e => setEp e { (← getEp e) with refs := epiId :: (← getEp e).refs }
  | .null => invariant "ep_attach_file: f_ep NULL after the install"
  -- spin_unlock(&file->f_lock)
  freeEphead toFree
  return 0

/-- `ep_alloc_epitem(ep, event, tfile, fd)` (:1755-1777): the user's watch
    quota (`percpu_counter_compare`, the inline of a kernel without
    `CONFIG_SMP`, percpu_counter.h:171-178), then the slab allocation. -/
def epAllocEpitem (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) : M (Except Int EpiId) := do
  let k ← getK
  let count := k.user.epollWatches
  let max := k.maxUserWatches
  let cmp : Int ← do
    if ← branch .percpuCounterCompareGt (count > max) then pure 1   -- folded into the `<` below
    else if ← branchCmp .percpuCounterCompareLt (count < max) count max then pure (-1)
    else pure 0
  if ← branch .epAllocEpitemOverWatches (cmp >= 0) then return .error (-ENOSPC)
  modifyK fun k => { k with user := { k.user with epollWatches := k.user.epollWatches + 1 } }
  if ← branch .epAllocEpitemNoMem (!(← hiddenAlloc .kmemCacheZallocEpi)) then
    modifyK fun k => { k with user := { k.user with epollWatches := k.user.epollWatches - 1 } }
    return .error (-ENOMEM)
  -- INIT_LIST_HEAD(&epi->rdllink); epi->ep = ep; ep_set_ffd; epi->event = *event; epi_clear_ovflist
  let id := (← getK).nextEpi
  setEpi id { ep, file := tfile, fd, fileAddr := 0, events := event.events, data := event.data }
  modifyK fun k => { k with nextEpi := id + 1 }
  return .ok id

/-- `ep_register_epitem(ep, epi, tep, full_check)` (:1795-1822). -/
def epRegisterEpitem (ep : EpId) (epiId : EpiId) (tep : Option EpId) (fullCheck : Bool) : M Int := do
  let tfile := (← getEpi epiId).file
  if ← branch .epRegisterEpitemTep tep.isSome then pure ()   -- mutex_lock_nested(&tep->mtx, 1)
  let error ← epAttachFile tfile epiId
  if ← branch .epRegisterEpitemAttachError (error != 0) then
    if ← branch .epRegisterEpitemAttachErrorTep tep.isSome then pure ()   -- mutex_unlock(&tep->mtx)
    freeEpi epiId   -- kmem_cache_free(epi_cache, epi)
    modifyK fun k => { k with user := { k.user with epollWatches := k.user.epollWatches - 1 } }
    return error
  if ← branchCmp .epRegisterEpitemFullCheck fullCheck (if fullCheck then 1 else 0) 0 then
    if ← branch .epRegisterEpitemNotTep tep.isNone then listFile tfile
  epRbtreeInsert ep epiId
  if ← branch .epRegisterEpitemTepUnlock tep.isSome then pure ()   -- mutex_unlock(&tep->mtx)
  epGet ep
  return 0

/-- `ep_insert(ep, event, tfile, fd, full_check)` (:1827-1904), with `mtx`
    held. -/
def epInsert (ep : EpId) (event : EpollEvent) (tfile : FileId) (fd : Int) (fullCheck : Bool) : M Int := do
  let tf ← getFile tfile
  let tep ← if ← branch .epInsertTargetEpoll (isFileEpoll tf) then some <$> epOf tf else pure none
  let r ← epAllocEpitem ep event tfile fd
  if ← branch .epInsertAllocError (r matches .error _) then
    return match r with | .error e => e | .ok _ => 0
  let .ok epiId := r | invariant "unreachable"
  let error ← epRegisterEpitem ep epiId tep fullCheck
  if ← branch .epInsertRegisterError (error != 0) then return error
  -- `full_check && reverse_path_check()`
  let tooMany ← do
    if ← branchCmp .epInsertFullCheck fullCheck (if fullCheck then 1 else 0) 0 then
      branch .epInsertReversePathFailed ((← reversePathCheck) != 0)
    else pure false
  if tooMany then
    epRemove ep epiId
    return -EINVAL
  let epi ← getEpi epiId
  if ← branchCmp .epInsertWakeup (hasFlag epi.events EPOLLWAKEUP) (epi.events &&& EPOLLWAKEUP).toNat 0 then
    unsupported "ep_create_wakeup_source: EPOLLWAKEUP survived ep_take_care_of_epollwakeup"
  -- epq.epi = epi; init_poll_funcptr(&epq.pt, ep_ptable_queue_proc)
  modifyK fun k => { k with epqEpi := some epiId }
  let revents ← epItemPollAt epiId { qproc := some epiId } 1
  -- ep_ptable_queue_proc() signals allocation failure by clearing epq.epi
  if ← branch .epInsertPwqAllocFailed (← getK).epqEpi.isNone then
    epRemove ep epiId
    return -ENOMEM
  modifyK fun k => { k with epqEpi := none }   -- epq leaves scope
  -- spin_lock_irq(&ep->lock)
  epSetBusyPollNapiId epiId
  let epi ← getEpi epiId
  let ready ← do
    if ← branchCmp .epInsertReady (revents != 0) revents.toNat 0 then branch .epInsertNotLinked (!epi.linked)
    else pure false
  let mut pwake := 0
  if ready then
    -- list_add_tail(&epi->rdllink, &ep->rdllist); ep_pm_stay_awake (empty)
    let e ← getEp ep
    setEp ep { e with rdllist := e.rdllist ++ [epiId] }
    setEpi epiId { epi with linked := true }
    if ← branch .epInsertWqActive (← waitqueueActive (.epWq ep)) then
      unsupported "wake_up(&ep->wq) at ep_insert: a task sleeping in epoll_wait (tier 2)"
    if ← branch .epInsertPollWaitActive (← waitqueueActive (.epPollWait ep)) then pwake := pwake + 1
  -- spin_unlock_irq(&ep->lock)
  if ← branch .epInsertPwake (pwake != 0) then epPollSafewake ep none 0
  return 0

/-- `ep_modify(ep, epi, event)` (:1910-1980), with `mtx` held: the mask and
    data are replaced, then the item is polled without registering. -/
def epModify (ep : EpId) (epiId : EpiId) (event : EpollEvent) : M Int := do
  let pt : PollTable := {}   -- init_poll_funcptr(&pt, NULL)
  let epi ← getEpi epiId
  setEpi epiId { epi with events := event.events, data := event.data }
  if ← branchCmp .epModifyWakeup (hasFlag event.events EPOLLWAKEUP) (event.events &&& EPOLLWAKEUP).toNat 0 then
    if ← branch .epModifyNoWakeupSource true then   -- !ep_has_wakeup_source(epi): ws is NULL
      unsupported "ep_create_wakeup_source: EPOLLWAKEUP survived ep_take_care_of_epollwakeup"
  else if ← branch .epModifyHasWakeupSource false then
    unsupported "ep_destroy_wakeup_source with a wakeup source"
  -- smp_mb()
  let revents ← epItemPollAt epiId pt 1
  let mut pwake := 0
  if ← branchCmp .epModifyReady (revents != 0) revents.toNat 0 then
    -- spin_lock_irq(&ep->lock)
    let epi ← getEpi epiId
    if ← branch .epModifyNotLinked (!epi.linked) then
      let e ← getEp ep
      setEp ep { e with rdllist := e.rdllist ++ [epiId] }
      setEpi epiId { epi with linked := true }
      if ← branch .epModifyWqActive (← waitqueueActive (.epWq ep)) then
        unsupported "wake_up(&ep->wq) at ep_modify: a task sleeping in epoll_wait (tier 2)"
      if ← branch .epModifyPollWaitActive (← waitqueueActive (.epPollWait ep)) then pwake := pwake + 1
    -- spin_unlock_irq(&ep->lock)
  if ← branch .epModifyPwake (pwake != 0) then epPollSafewake ep none 0
  return 0

/-! ## Delivery (:1993-2101) -/

/-- `epoll_put_uevent(revents, data, uevent)` (include/linux/eventpoll.h:78-86)
    for x86-64: the packed 12 bytes, `events` then `data`, little-endian;
    the caller's buffer is valid (the guest's). -/
def epollPutUevent (revents : UInt32) (data : UInt64) : M (Option ByteArray) := do
  if ← branch .epollPutUeventEventsFault false then return none
  if ← branch .epollPutUeventDataFault false then return none
  let le (v : Nat) (width : Nat) : List UInt8 := (List.range width).map fun k => UInt8.ofNat (v / 256 ^ k % 256)
  return some (ByteArray.mk (le revents.toNat 4 ++ le data.toNat 8).toArray)

/-- `ep_deliver_event(ep, epi, pt, &uevents, &scan_batch)` (:1994-2056):
    1 with the event's bytes, 0 when the re-poll found nothing, -EFAULT
    (unreached) with the item back at the batch's head. The `ws` block
    (:2009-2014) is dead without `CONFIG_PM`. -/
def epDeliverEvent (ep : EpId) (epiId : EpiId) (pt : PollTable) : M (Int × ByteArray) := do
  -- list_del_init(&epi->rdllink): the item leaves the scan batch
  setEpi epiId { (← getEpi epiId) with linked := false }
  let revents ← epItemPollAt epiId pt 1
  if ← branchCmp .epDeliverEventNotReady (revents == 0) revents.toNat 0 then return (0, ByteArray.empty)
  let epi ← getEpi epiId
  let next ← epollPutUevent revents epi.data
  if ← branch .epDeliverEventPutFault next.isNone then
    unsupported "copy_to_user faulted in epoll_put_uevent (the guest's buffer is valid)"
  let bytes := next.get!
  if ← branchCmp .epDeliverEventOneshot (hasFlag epi.events EPOLLONESHOT) (epi.events &&& EPOLLONESHOT).toNat 0 then
    setEpi epiId { epi with events := epi.events &&& EP_PRIVATE_BITS }
  -- `!(events & EPOLLET)`: bit 31, the sign test `(int)events >= 0` in the built code
  else if ← branchCmp .epDeliverEventLevelTriggered (!hasFlag epi.events EPOLLET) epi.events.toNat 0 then
    -- list_add_tail(&epi->rdllink, &ep->rdllist); ep_pm_stay_awake (empty)
    let e ← getEp ep
    setEp ep { e with rdllist := e.rdllist ++ [epiId] }
    setEpi epiId { (← getEpi epiId) with linked := true }
  return (1, bytes)

/-- `ep_send_events(ep, events, maxevents)` (:2057-2101): the count
    delivered and the bytes written to the caller's buffer. -/
def epSendEvents (ep : EpId) (maxevents : Int) : M (Int × ByteArray) := do
  if ← branch .epSendEventsFatalSignal false then return (-EINTR, ByteArray.empty)   -- no signal pending (design 5)
  let pt : PollTable := {}   -- init_poll_funcptr(&pt, NULL)
  -- mutex_lock(&ep->mtx)
  let batch ← epStartScan ep
  let mut res : Int := 0
  let mut out := ByteArray.empty
  let mut remaining := batch
  let mut broke := false
  for epiId in batch do
    _ ← branch .epSendEventsIter true
    if ← branch .epSendEventsFull (res >= maxevents) then   -- folded on the first iteration
      broke := true
      break
    let (delivered, bytes) ← epDeliverEvent ep epiId pt
    remaining := remaining.erase epiId
    if ← branch .epSendEventsDeliverError (delivered < 0) then
      if ← branch .epSendEventsFirstError (res == 0) then res := delivered
      broke := true
      break
    res := res + delivered
    out := out ++ bytes
  if !broke then _ ← branch .epSendEventsIter false
  epDoneScan ep remaining
  -- mutex_unlock(&ep->mtx)
  return (res, out)

/-! ## Waiting (:2103-2282, :2641-2691) -/

/-- `ep_timeout_to_timespec(&to, ms)` (:2103-2123): NULL for a negative
    timeout, zero for 0; a positive one reads the clock (`ktime_get_ts64`,
    :2120), tier 2. -/
def epTimeoutToTimespec (ms : Int) : M (Option Timespec64) := do
  if ← branchCmp .epTimeoutNegative (ms < 0) ms 0 then return none
  if ← branchCmp .epTimeoutZero (ms == 0) ms 0 then return some ⟨0, 0⟩
  unsupported "a positive epoll_wait timeout: ktime_get_ts64 and the sleep (tier 2)"

/-- `ep_events_available(ep)` (:576-582): `read_seqcount_begin`'s
    odd-sequence spin (the macro, attributed to :578), `list_empty_careful`
    of the ready list, `ep_is_scanning`, and `read_seqcount_retry`
    (`do___read_seqcount_retry`, seqlock.h:365-368). With one task the
    sequence is even and unchanged. -/
def epEventsAvailable (ep : EpId) : M Bool := do
  let e ← getEp ep
  if ← branchCmp .epEventsAvailableSeqOdd (e.seq % 2 == 1) (e.seq % 2) 0 then
    invariant "an odd seqcount outside a scan (a writer in progress)"
  let seq := e.seq
  if ← branch .epEventsAvailableRdllist (!e.rdllist.isEmpty) then return true
  if ← branch .epEventsAvailableScanning e.ovflist.isSome then
    invariant "ep_events_available while the set is scanning (a second task)"
  if ← branchCmp .epEventsAvailableSeqRetry ((← getEp ep).seq != seq) (← getEp ep).seq seq then
    invariant "a seqcount retry at ep_events_available (a concurrent scan)"
  return false

/-- `ep_poll(ep, events, maxevents, timeout)` (:2160-2282) for the paths
    tier 1 models: a zero timeout returns after one delivery attempt;
    anything that would sleep stops. -/
def epPoll (ep : EpId) (maxevents : Int) (timeout : Option Timespec64) : M (Int × ByteArray) := do
  let mut timedOut := false
  -- `timeout && (timeout->tv_sec | timeout->tv_nsec)`
  let positive ← do
    if ← branch .epPollHasTimeout timeout.isSome then
      let t := timeout.get!
      -- `tv_sec | tv_nsec`: both non-negative here (ep_timeout_to_timespec)
      let orv : Int := t.tvSec.toNat ||| t.tvNsec.toNat
      branchCmp .epPollTimeoutNonzero (orv != 0) orv 0
    else pure false
  if positive then unsupported "a positive epoll_wait timeout: select_estimate_accuracy (tier 2)"
  else if ← branch .epPollTimeoutAgain timeout.isSome then timedOut := true
  let eavail ← epEventsAvailable ep
  -- while (1): the first iteration; a second needs a sleep or a busy loop
  let mut result : Option (Int × ByteArray) := none
  if ← branchCmp .epPollEavail eavail (if eavail then 1 else 0) 0 then
    let (res, out) ← epSendEvents ep maxevents
    if ← branch .epPollSent (res != 0) then result := some (res, out)   -- folded after the maxevents break
  if let some r := result then return r
  if ← branchCmp .epPollTimedOut timedOut (if timedOut then 1 else 0) 0 then return (0, ByteArray.empty)
  unsupported "epoll_wait would sleep: ep_busy_loop, signal_pending and the wait on ep->wq (tier 2)"

/-- `do_epoll_wait(epfd, events, maxevents, to)` (:2641-2682). The events
    delivered go to the caller's buffer (`World.userOut`). -/
def doEpollWait (epfd : Nat) (maxevents : Int) (to : Option Timespec64) : M Int := do
  -- one unsigned range check in the built code, `(unsigned)(maxevents - 1) >
  -- EP_MAX_EVENTS - 1`, its operands on the second decision
  let bad ← do
    if ← branch .doEpollWaitMaxeventsNonpositive (maxevents <= 0) then pure true
    else branchCmp .doEpollWaitMaxeventsTooMany (maxevents > EP_MAX_EVENTS)
           ((maxevents - 1) % 4294967296) (EP_MAX_EVENTS - 1)
  if bad then return -EINVAL
  -- access_ok(events, maxevents * sizeof(struct epoll_event)): the guest's buffer
  if ← branch .doEpollWaitAccessNotOk false then return -EFAULT
  let f ← fdget epfd
  if ← branch .doEpollWaitNoFile f.file.isNone then return -EBADF
  let fid := f.file.get!
  let mut error : Int := -EINVAL
  if ← branch .doEpollWaitNotEpoll (!isFileEpoll (← getFile fid)) then pure ()   -- goto error_fput
  else
    let ep ← epOf (← getFile fid)
    let (res, out) ← epPoll ep maxevents to
    error := res
    modify fun w => { w with userOut := some out }
  fdput f   -- error_fput:
  return error

/-! ## epoll_ctl (:2454-2636) -/

/-- `epoll_mutex_lock(mutex, depth, nonblock)` (:2467-2477): the syscall
    passes `nonblock = false`, so `mutex_lock_nested` (a cut) and 0. -/
def epollMutexLock (nonblock : Bool) : M Int := do
  if ← branch .epollMutexLockBlocking (!nonblock) then return 0   -- mutex_lock_nested(mutex, depth)
  unsupported "epoll_mutex_lock with nonblock (io_uring's epoll_ctl)"

/-- `ep_loop_check_proc(ep, depth)` (:2295-2334): the depth of the subtree
    under `ep`, or more than `EP_MAX_NESTS` for a loop through
    `inserting_into` or too deep a chain; a set visited in this check
    answers its cached depth; non-epoll files met are listed for the
    reverse check. `loop_check_gen` is the relative counter (design 3.5). -/
def epLoopCheckProc : Nat → EpId → Nat → M Nat
  | 0, _, _ => invariant "ep_loop_check_proc nested beyond EP_MAX_NESTS + 2"
  | fuel + 1, ep, depth => do
    let e ← getEp ep
    let gen := (← getK).loopCheckGen
    if ← branchCmpExcluded .epLoopCheckProcVisited (e.gen == gen) .loopCheckGen then return e.loopCheckDepth
    -- mutex_lock_nested(&ep->mtx, depth + 1)
    setEp ep { e with gen }
    let mut result := 0
    let mut broke := false
    for (_, epiId) in e.rbr do
      _ ← branch .epLoopCheckProcIter true
      let epi ← getEpi epiId
      let file ← getFile epi.file
      if ← branch .epLoopCheckProcItemEpoll (isFileEpoll file) then
        let tovisit ← epOf file
        -- `ep_tovisit == inserting_into || depth > EP_MAX_NESTS`
        let bad ← do
          if ← branch .epLoopCheckProcSelf ((← getK).insertingInto == some tovisit) then pure true
          else branchCmp .epLoopCheckProcTooDeep (depth > EP_MAX_NESTS) depth EP_MAX_NESTS
        if bad then result := EP_MAX_NESTS + 1
        else
          let sub := (← epLoopCheckProc fuel tovisit (depth + 1)) + 1
          -- max(result, sub)
          result ← if ← branch .epLoopCheckProcMax (result > sub) then pure result else pure sub   -- a MAX_EXPR
        if ← branch .epLoopCheckProcOver (result > EP_MAX_NESTS) then   -- folded on the constant path
          broke := true
          break
      else listFile epi.file
    if !broke then _ ← branch .epLoopCheckProcIter false
    setEp ep { (← getEp ep) with loopCheckDepth := result }
    -- mutex_unlock(&ep->mtx)
    return result

/-- `ep_get_upwards_depth_proc(ep, depth)` (:2338-2351): the depth of the
    sets above `ep`, through `refs`. -/
def epGetUpwardsDepthProc : Nat → EpId → Nat → M Nat
  | 0, _, _ => invariant "ep_get_upwards_depth_proc nested beyond EP_MAX_NESTS + 2"
  | fuel + 1, ep, depth => do
    let e ← getEp ep
    let gen := (← getK).loopCheckGen
    if ← branchCmpExcluded .epGetUpwardsDepthProcVisited (e.gen == gen) .loopCheckGen then return e.loopCheckDepth
    let mut result := 0
    for epiId in e.refs do
      _ ← branch .epGetUpwardsDepthProcIter true
      let sub := (← epGetUpwardsDepthProc fuel (← getEpi epiId).ep (depth + 1)) + 1
      result ← if ← branch .epGetUpwardsDepthProcMax (result > sub) then pure result else pure sub   -- a MAX_EXPR
    _ ← branch .epGetUpwardsDepthProcIter false
    setEp ep { (← getEp ep) with gen, loopCheckDepth := result }
    return result

/-- `ep_loop_check(ep, to)` (:2363-2382). -/
def epLoopCheck (ep to : EpId) : M Int := do
  modifyK fun k => { k with insertingInto := some ep }
  let depth ← epLoopCheckProc (EP_MAX_NESTS + 2) to 0
  if ← branchCmp .epLoopCheckTooDeep (depth > EP_MAX_NESTS) depth EP_MAX_NESTS then return -1
  -- rcu_read_lock(); ... rcu_read_unlock()
  let upwards ← epGetUpwardsDepthProc (EP_MAX_NESTS + 2) ep 0
  if ← branchCmp .epLoopCheckTotalTooDeep (depth + 1 + upwards > EP_MAX_NESTS) (depth + 1 + upwards) EP_MAX_NESTS then
    return -1
  return 0

/-- The body of `do_epoll_ctl` between the two `fdget`s and the
    `error_tgt_fput` exit: the error and whether a full check was begun. -/
private def doEpollCtlBody (fId tId : FileId) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) :
    M (Int × Bool) := do
  let fFile ← getFile fId
  let tFile ← getFile tId
  -- `!file_can_poll(fd_file(tf))`: `f_op->poll` NULL (modelled, unexercised: design 9.3)
  if ← branch .doEpollCtlCannotPoll (!(← fopsOf tFile.fOp).poll) then return (-EPERM, false)
  let mut events := events
  -- ep_op_has_event(op): `op != EPOLL_CTL_DEL`; ep_take_care_of_epollwakeup without CONFIG_PM_SLEEP
  if ← branchCmp .doEpollCtlHasEvent (op != EPOLL_CTL_DEL) op EPOLL_CTL_DEL then events := events &&& ~~~EPOLLWAKEUP
  -- error = -EINVAL; `fd_file(f) == fd_file(tf) || !is_file_epoll(fd_file(f))`
  let bad ← do
    if ← branch .doEpollCtlSameFile (fId == tId) then pure true
    else branch .doEpollCtlNotEpoll (!isFileEpoll fFile)
  if bad then return (-EINVAL, false)
  -- EPOLLEXCLUSIVE at ADD time only, never on an epoll target, only its OK bits
  let exclusiveBad ← do
    if ← branch .doEpollCtlExclusiveHasEvent (op != EPOLL_CTL_DEL) then
      if ← branchCmp .doEpollCtlExclusive (hasFlag events EPOLLEXCLUSIVE) (events &&& EPOLLEXCLUSIVE).toNat 0 then
        if ← branchCmp .doEpollCtlExclusiveMod (op == EPOLL_CTL_MOD) op EPOLL_CTL_MOD then pure true
        else if ← branchCmp .doEpollCtlExclusiveAdd (op == EPOLL_CTL_ADD) op EPOLL_CTL_ADD then
          if ← branch .doEpollCtlExclusiveTargetEpoll (isFileEpoll tFile) then pure true
          else branchCmp .doEpollCtlExclusiveBadBits (events &&& ~~~EPOLLEXCLUSIVE_OK_BITS != 0)
                 (events &&& ~~~EPOLLEXCLUSIVE_OK_BITS).toNat 0
        else pure false
      else pure false
    else pure false
  if exclusiveBad then return (-EINVAL, false)
  let ep ← epOf fFile
  let error ← epollMutexLock false   -- epoll_mutex_lock(&ep->mtx, 0, nonblock)
  if ← branch .doEpollCtlLockError (error != 0) then return (error, false)
  let mut fullCheck := false
  let mut tep : Option EpId := none
  if ← branch .doEpollCtlIsAdd (op == EPOLL_CTL_ADD) then   -- folded after the exclusive block
    let e ← getEp ep
    -- `f->f_ep || ep->gen == loop_check_gen || is_file_epoll(tf)`
    let nested ← do
      if ← branch .doEpollCtlEpfdWatched (fFile.fEp != .null) then pure true
      else if ← branchCmpExcluded .doEpollCtlGenMatches (e.gen == (← getK).loopCheckGen) .loopCheckGen then
        invariant "a set's gen equal to loop_check_gen outside a check: the fixture's warm-up rule (design 3.5)"
      else branch .doEpollCtlTargetEpoll (isFileEpoll tFile)
    if nested then
      -- mutex_unlock(&ep->mtx); epoll_mutex_lock(&epnested_mutex, 0, nonblock)
      let error ← epollMutexLock false
      if ← branch .doEpollCtlNestedLockError (error != 0) then return (error, false)
      modifyK fun k => { k with loopCheckGen := k.loopCheckGen + 1 }
      fullCheck := true
      if ← branch .doEpollCtlTargetEpollLoop (isFileEpoll tFile) then
        tep := some (← epOf tFile)
        -- error = -ELOOP
        if ← branch .doEpollCtlEloop ((← epLoopCheck ep tep.get!) != 0) then return (-ELOOP, true)
      let error ← epollMutexLock false   -- epoll_mutex_lock(&ep->mtx, 0, nonblock)
      if ← branch .doEpollCtlRelockError (error != 0) then return (error, true)
  let epi ← epFind ep tId fd
  let mut error : Int := -EINVAL
  -- switch (op): one choice point in the C, lowered to one compare and a jump table;
  -- the three arms are plain decisions (no per-arm compare exists in the built code:
  -- the same-record rule of the mutation campaign showed all three matching one record)
  if ← branch .doEpollCtlCaseAdd (op == EPOLL_CTL_ADD) then
    if ← branch .doEpollCtlAddAbsent epi.isNone then
      events := events ||| EPOLLERR ||| EPOLLHUP
      error ← epInsert ep ⟨events, data⟩ tId fd fullCheck
    else error := -EEXIST
  else if ← branch .doEpollCtlCaseDel (op == EPOLL_CTL_DEL) then
    if ← branch .doEpollCtlDelPresent epi.isSome then
      epRemove ep epi.get!
      error := 0
    else error := -ENOENT
  else if ← branch .doEpollCtlCaseMod (op == EPOLL_CTL_MOD) then
    if ← branch .doEpollCtlModPresent epi.isSome then
      let item ← getEpi epi.get!
      if ← branchCmp .doEpollCtlModNotExclusive (!hasFlag item.events EPOLLEXCLUSIVE) (item.events &&& EPOLLEXCLUSIVE).toNat 0 then
        events := events ||| EPOLLERR ||| EPOLLHUP
        error ← epModify ep epi.get! ⟨events, data⟩
    else error := -ENOENT
  -- mutex_unlock(&ep->mtx)
  return (error, fullCheck)

/-- `do_epoll_ctl(epfd, op, fd, epds, nonblock)` (:2479-2619). The two
    `CLASS(fd, ..)` descriptors are put at the exit in reverse order, on
    every path (an empty one records `fdput`'s decision as false). -/
def doEpollCtl (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) : M Int := do
  let f ← fdget epfd
  if ← branch .doEpollCtlEpfdEmpty f.file.isNone then
    fdput f
    return -EBADF
  let tf ← fdget (fd % 4294967296).toNat   -- `unsigned int fd`: the low 32 bits
  if ← branch .doEpollCtlFdEmpty tf.file.isNone then
    fdput tf
    fdput f
    return -EBADF
  let (error, fullCheck) ← doEpollCtlBody f.file.get! tf.file.get! op fd events data
  -- error_tgt_fput:
  if ← branch .doEpollCtlFullCheckExit fullCheck then   -- threaded away on the early exits
    clearTfileCheckList
    modifyK fun k => { k with loopCheckGen := k.loopCheckGen + 1 }
    -- mutex_unlock(&epnested_mutex)
  fdput tf
  fdput f
  return error

/-- `SYSCALL_DEFINE4(epoll_ctl, ...)` (:2626-2636): the event is copied
    from the caller for every op but DEL (the guest's buffer is valid). -/
def sysEpollCtl (epfd : Nat) (op : Int) (fd : Int) (events : UInt32) (data : UInt64) : M Int := do
  if ← branchCmp .sysEpollCtlHasEvent (op != EPOLL_CTL_DEL) op EPOLL_CTL_DEL then
    if ← branch .sysEpollCtlCopyFault false then return -EFAULT
  doEpollCtl epfd op fd events data

/-- `SYSCALL_DEFINE1(epoll_create1, int, flags)` (:2441-2444). -/
def sysEpollCreate1 (flags : UInt32) : M Int := doEpollCreate flags

/-- `SYSCALL_DEFINE4(epoll_wait, ...)` (:2684-2691): the timespec argument
    is computed before the call. -/
def sysEpollWait (epfd : Nat) (maxevents timeout : Int) : M Int := do
  let to ← epTimeoutToTimespec timeout
  doEpollWait epfd maxevents to

end Leanux
