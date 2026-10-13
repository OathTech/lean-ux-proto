#!/usr/bin/env python3
"""Generate kernel/patches/choice-stream.patch from the locked source.

Run from the repository root: copies the touched files from .deps/linux into
.artifacts/choice-patch/{base,new}, edits `new`, and writes the unified diff.
The patch applies to the pristine tree (scripts/apply-kernel-patch.py); it
touches no file the check anchors (correspondence/kcov.json "files").
Edits: kcov_choice_ip and steering (choice-stream strategy, steps 1-2); the
random and clock hooks; dispatch sections in process_one_work and the NET_RX
vector (D1 sprint, stream A); a resched record when cond_resched schedules
inside a task's dispatch section (D1 integration); timer dispatch sections at
call_timer_fn, the kind-303 arm record at mod_timer and the virtual time
advance (KCOV_LEANUX_TIME_ADVANCE, kind 304) (D3, docs/2026-10-05-d3-timers.md);
the allocation hook in slab_alloc_node and __alloc_pages_noprof, kind 305, its
load ioctl with the inventory mode (KCOV_LEANUX_ALLOC_LOAD, 205) and status
ioctl (206) (A stream K1, docs/2026-10-05-a-alloc.md, section 4); the
dispatch set's capacity KCOV_DISPATCH_MAX 32 (D3+A integration); the dispatch
identity (docs/2026-10-11-dispatch-order.md): the kind-300 start record's
second word names the dispatched unit (the work item's or timer's address, 0
for a softirq), the kind-303 arm record's third word the timer, and the
kind-307 queue record at __queue_work {work, func} the unit a recording
context queued, so the mirror follows the dispatch order instead of assuming
queue order. Record-only. W9 (docs/2026-10-06-w8-w9-netns-routing.md,
section 4.1): the kind-306 record of the `jiffies` the dst cache stores, at
`dst_cache_reset` (include/net/dst_cache.h, inline: `_THIS_IP_`, resolved
through the inline chain) and at the refresh on a miss (net/core/dst_cache.c,
`dst_cache_per_cpu_get`'s fail label), gated by KCOV_DISPATCH_ARM_RECORDS like
the arm record; the mirror computes the cache's `time_after` from the two
recorded values. Record-only.
epoll stream R (docs/2026-10-12-epoll-design.md, section 3.2): the kind-308
record of the `struct file` address an item is keyed by, at ep_rbtree_insert
(fs/eventpoll.c:1585, `_THIS_IP_`), once per call, which is every
EPOLL_CTL_ADD that reaches the tree (one that reverse_path_check or a pwq
allocation failure then undoes included), 8 bytes; the mirror orders its
items by (recorded address, fd) as ep_cmp_ffd does. Line-preserving (stream
T): fs/eventpoll.c keeps its pristine line count, so the oracle's DWARF lines
for that file are the pristine tree's.
Written in any recording context (an FS trace loads no dispatch set, so the
arm-record gate of kinds 303/306/307 is unavailable to it). Record-only.
seccomp stream W (docs/2026-10-12-seccomp-design.md, section 3.3): the kind-309
records of the eBPF program the classic-to-eBPF translation writes, at the
end of bpf_migrate_filter's second pass (net/core/filter.c, `_THIS_IP_`),
before bpf_prog_select_runtime locks the pages: one record with the eBPF
length, then one record per emitted bpf_insn (the instruction), all 8 bytes
from one call site, in any recording context like kind 308. One site, not a
site per record type: two `_THIS_IP_` labels a line apart resolved to one
address under optimisation (step 0), and the check keys a site by its
consumer frame and one record length. The mirror checks the length first,
then its own translation instruction by instruction, so a mismatch names
the first differing instruction. Record-only. Line-preserving: net/core/
filter.c is an anchored file and the checker reads its statements from the
pristine source while DWARF carries the built source's lines, so the hook
adds no include and no line: an extern declaration and the call share the
line of `fp = bpf_prog_select_runtime(fp, &err);` (1315 in both sources).
Review item 7 (docs/2026-10-13-review-items-7-8.md, section 5): the end of
a guest wait as a record, KCOV_LEANUX_JIFFIES (207): jiffies_64 read and
written as kind 310 {jiffies} (8 bytes) into the remote area of the
process's common handle (kcov_jiffies_read; kcov_choice_write split into
the area writer and its wrapper). In any recording context. Record-only;
kernel/kcov.c is not an anchored file.
"""
import sys, re, os, shutil, subprocess
WD='.artifacts/choice-patch'; N=WD+'/new'
SOURCE=os.environ.get('LEANUX_SHARED_ROOT', '.') + '/.deps/linux'
TOUCHED=['kernel/kcov.c','include/linux/kcov.h','include/linux/sched.h','drivers/char/random.c',
         'kernel/time/timekeeping.c','kernel/workqueue.c','kernel/softirq.c','kernel/sched/core.c',
         'kernel/time/timer.c','mm/slub.c','mm/page_alloc.c',
         'include/net/dst_cache.h','net/core/dst_cache.c',
         'fs/eventpoll.c',
         'net/core/filter.c']
shutil.rmtree(WD, ignore_errors=True)
for side in ('base', 'new'):
    for f in TOUCHED:
        os.makedirs(os.path.dirname(f'{WD}/{side}/{f}'), exist_ok=True)
        shutil.copyfile(f'{SOURCE}/{f}', f'{WD}/{side}/{f}')
def rd(f): return open(os.path.join(N,f)).read()
def wr(f,s): open(os.path.join(N,f),'w').write(s)
def sub(f,a,b,n=1):
    s=rd(f); assert s.count(a)==n,(f,a,s.count(a)); wr(f,s.replace(a,b))
s = rd('kernel/kcov.c').rstrip('\n') + r'''

/*
 * LEANUX: a choice the C consumes (a random draw, a clock read), recorded at
 * a generic interception point into the active KCOV area
 * (docs/2026-10-03-choice-stream-strategy.md). The record carries the kind,
 * the consumer's return address, a sequence number that orders records
 * across the task and remote streams, the value's length and up to 40 value
 * bytes. Coverage mode: a header word (KCOV_CHOICE_MAGIC in bits 48-63, the
 * length in 32-47, the kind in 16-31, the payload words in 0-15), the call
 * site, the sequence number, then the payload. Comparison mode: a header
 * record (type bit 63 | KCOV_CHOICE_MAGIC << 32 | kind << 16 | words; call
 * site; sequence number; length), then records of three payload words
 * (KCOV_CHOICE_MAGIC + 1). A record that does not fit marks the area full,
 * so the harness fails noisily instead of losing a value.
 */
#define KCOV_CHOICE_MAGIC 0x4c5aULL
#define KCOV_CHOICE_MAX_WORDS 5
static atomic64_t kcov_choice_seq;

/*
 * LEANUX steering (choice-stream strategy, step 2): a trace may supply the
 * values of choices at named call sites. The guest's parent loads a schedule
 * on its remote KCOV fd (KCOV_LEANUX_STEER_LOAD) before it forks the trace
 * process; a trace with no remote instance (an FS trace, A2) loads it on its
 * own task instance before KCOV_ENABLE, and that schedule is consulted in
 * the task's own context (a network trace's task instance has none). The
 * schedule covers every encounter of the call sites it names, in order: each
 * entry gives the site's return addresses and kind, and either a value to
 * substitute or "draw" (keep the kernel's value). A hook at a named site that
 * does not match the head entry is a mismatch: a marker record is written and
 * the entry stays. Other sites are not steered. The loader reads the
 * remaining entries and mismatches back (KCOV_LEANUX_STEER_STATUS). Only recording contexts consult the schedule.
 */
#define KCOV_STEER_MAX 64
#define KCOV_STEER_IPS 4
struct kcov_steer_entry {
	u64 ips[KCOV_STEER_IPS];
	u32 kind;
	u32 len;
	u32 draw;
	u32 pad;
	u8 value[40];
};
struct kcov_steer {
	spinlock_t lock;
	u32 n, head, mismatches;
	struct kcov_steer_entry e[KCOV_STEER_MAX];
};

static struct kcov_steer *kcov_steer_find(struct task_struct *t)
{
	struct kcov_remote *remote;
	struct kcov_steer *steer = NULL;
	unsigned long flags;

	if (t->kcov && t->kcov->remote)
		return t->kcov->steer;		/* inside a remote section */
	if (t->kcov && t->kcov->steer)
		return t->kcov->steer;		/* the task's own instance (A2: FS traces) */
	if (!t->kcov_handle)
		return NULL;
	spin_lock_irqsave(&kcov_remote_lock, flags);
	remote = kcov_remote_find(t->kcov_handle);
	if (remote)
		steer = remote->kcov->steer;	/* the trace process's own context */
	spin_unlock_irqrestore(&kcov_remote_lock, flags);
	return steer;
}

static bool kcov_steer_names(struct kcov_steer *steer, unsigned long ip)
{
	u32 i, j;

	for (i = 0; i < steer->n; i++)
		for (j = 0; j < KCOV_STEER_IPS; j++)
			if (steer->e[i].ips[j] == ip)
				return true;
	return false;
}

/* 1: steered, 0: not steered, -1: a mismatch at a named site */
static int kcov_steer_apply(struct task_struct *t, u32 kind, unsigned long ip, void *data, unsigned int len)
{
	struct kcov_steer *steer = kcov_steer_find(t);
	struct kcov_steer_entry *e;
	unsigned long flags;
	int ret = 0;
	u32 j;

	if (!steer)
		return 0;
	spin_lock_irqsave(&steer->lock, flags);
	if (!kcov_steer_names(steer, ip))
		goto out;
	e = steer->head < steer->n ? &steer->e[steer->head] : NULL;
	if (e && e->kind == kind && (e->draw || e->len == len))
		for (j = 0; j < KCOV_STEER_IPS; j++)
			if (e->ips[j] == ip) {
				if (!e->draw) {
					memcpy(data, e->value, len);
					ret = 1;
				}
				steer->head++;
				goto out;
			}
	steer->mismatches++;
	ret = -1;
out:
	spin_unlock_irqrestore(&steer->lock, flags);
	return ret;
}

static void kcov_choice_write(struct task_struct *t, u32 kind, unsigned long ip, const void *data, unsigned int len);

void notrace kcov_choice_ip(u32 kind, unsigned long ip, void *data, unsigned int len)
{
	struct task_struct *t = current;
	int steered;

	if (!check_kcov_mode(KCOV_MODE_TRACE_PC, t) &&
	    !(IS_ENABLED(CONFIG_KCOV_ENABLE_COMPARISONS) && check_kcov_mode(KCOV_MODE_TRACE_CMP, t)))
		return;
	/* values longer than a record's 40 bytes are never steered */
	steered = len <= 40 ? kcov_steer_apply(t, kind, canonicalize_ip(ip), data, len) : 0;
	if (steered < 0)
		kcov_choice_write(t, 0xffff, ip, NULL, 0);	/* the mismatch marker */
	kcov_choice_write(t, kind | (steered > 0 ? 0x8000 : 0), ip, data, len);
}
EXPORT_SYMBOL(kcov_choice_ip);

/* LEANUX review item 7 (docs/2026-10-13-review-items-7-8.md, section 5): the
 * writer over an explicit area, mode and size, so that the trace task can
 * also append a record to the remote area of its common handle (kind 310,
 * kcov_jiffies_read). kcov_choice_write is the wrapper over the task's own. */
static void notrace kcov_choice_write_area(struct task_struct *t, enum kcov_mode mode, u64 *area, unsigned int size, u32 kind, unsigned long ip, const void *data, unsigned int len)
{
	const u8 *bytes = data;
	u64 words[KCOV_CHOICE_MAX_WORDS + 1] = {0};
	unsigned int n = len > 8 * KCOV_CHOICE_MAX_WORDS ? 8 * KCOV_CHOICE_MAX_WORDS : len;
	unsigned int nwords = DIV_ROUND_UP(n, 8), i;
	u64 seq;

	if (mode == KCOV_MODE_TRACE_PC) {
		u64 pos;

		for (i = 0; i < n; i++)
			words[i / 8] |= (u64)bytes[i] << (8 * (i % 8));
		pos = READ_ONCE(area[0]);
		if (pos + 3 + nwords >= size) {
			WRITE_ONCE(area[0], size - 1);
			return;
		}
		seq = atomic64_inc_return(&kcov_choice_seq);
		WRITE_ONCE(area[0], pos + 3 + nwords);
		barrier();
		area[pos + 1] = KCOV_CHOICE_MAGIC << 48 | (u64)(len & 0xffff) << 32 |
				(u64)(kind & 0xffff) << 16 | nwords;
		area[pos + 2] = canonicalize_ip(ip);
		area[pos + 3] = seq;
		for (i = 0; i < nwords; i++)
			area[pos + 4 + i] = words[i];
	} else if (IS_ENABLED(CONFIG_KCOV_ENABLE_COMPARISONS) &&
		   mode == KCOV_MODE_TRACE_CMP) {
		u64 count, start, nrec = 1 + DIV_ROUND_UP(nwords, 3), r;

		for (i = 0; i < n; i++)
			words[i / 8] |= (u64)bytes[i] << (8 * (i % 8));
		count = READ_ONCE(area[0]);
		start = 1 + count * KCOV_WORDS_PER_CMP;
		if ((start + nrec * KCOV_WORDS_PER_CMP) * sizeof(u64) >
		    size * sizeof(unsigned long)) {
			WRITE_ONCE(area[0], (size - 1) / KCOV_WORDS_PER_CMP);
			return;
		}
		seq = atomic64_inc_return(&kcov_choice_seq);
		WRITE_ONCE(area[0], count + nrec);
		barrier();
		area[start] = 1ULL << 63 | KCOV_CHOICE_MAGIC << 32 | (u64)(kind & 0xffff) << 16 | nwords;
		area[start + 1] = canonicalize_ip(ip);
		area[start + 2] = seq;
		area[start + 3] = len;
		for (r = 0; r + 1 < nrec; r++) {
			u64 *rec = area + start + (r + 1) * KCOV_WORDS_PER_CMP;

			rec[0] = 1ULL << 63 | (KCOV_CHOICE_MAGIC + 1) << 32 | r;
			rec[1] = words[3 * r];
			rec[2] = words[3 * r + 1];
			rec[3] = 3 * r + 2 <= KCOV_CHOICE_MAX_WORDS ? words[3 * r + 2] : 0;
		}
	}
}

static void notrace kcov_choice_write(struct task_struct *t, u32 kind, unsigned long ip, const void *data, unsigned int len)
{
	if (check_kcov_mode(KCOV_MODE_TRACE_PC, t))
		kcov_choice_write_area(t, KCOV_MODE_TRACE_PC, (u64 *)t->kcov_area, t->kcov_size, kind, ip, data, len);
	else if (IS_ENABLED(CONFIG_KCOV_ENABLE_COMPARISONS) && check_kcov_mode(KCOV_MODE_TRACE_CMP, t))
		kcov_choice_write_area(t, KCOV_MODE_TRACE_CMP, (u64 *)t->kcov_area, t->kcov_size, kind, ip, data, len);
}
'''
wr('kernel/kcov.c', s)
sub('kernel/kcov.c', """	int			sequence;
};
""", """	int			sequence;
	/* LEANUX: the trace's steering schedule (see kcov_choice_ip). */
	struct kcov_steer	*steer;
};
""")
sub('kernel/kcov.c', """		kcov_remote_reset(kcov);
		vfree(kcov->area);
		kfree(kcov);""", """		kcov_remote_reset(kcov);
		vfree(kcov->area);
		kfree(kcov->steer);
		kfree(kcov);""")
sub('kernel/kcov.c', """static long kcov_ioctl(struct file *filep, unsigned int cmd, unsigned long arg)
{""", """#define KCOV_LEANUX_STEER_LOAD		_IOW('c', 200, unsigned long)
#define KCOV_LEANUX_STEER_STATUS	_IOR('c', 201, unsigned long)
static long kcov_steer_load(struct kcov *kcov, void __user *arg);
static long kcov_steer_status(struct kcov *kcov, void __user *arg);

static long kcov_ioctl(struct file *filep, unsigned int cmd, unsigned long arg)
{""")
sub('kernel/kcov.c', """	case KCOV_REMOTE_ENABLE:
		if (get_user(remote_num_handles,""", """	case KCOV_LEANUX_STEER_LOAD:
		return kcov_steer_load(kcov, (void __user *)arg);
	case KCOV_LEANUX_STEER_STATUS:
		return kcov_steer_status(kcov, (void __user *)arg);
	case KCOV_REMOTE_ENABLE:
		if (get_user(remote_num_handles,""")
s2 = rd('kernel/kcov.c').rstrip('\n') + """

/* LEANUX: load a schedule: { u32 n; u32 pad; struct kcov_steer_entry e[n]; } */
static long kcov_steer_load(struct kcov *kcov, void __user *arg)
{
	struct kcov_steer *steer, *old;
	unsigned long flags;
	u32 n, i;

	if (get_user(n, (u32 __user *)arg))
		return -EFAULT;
	if (n > KCOV_STEER_MAX)
		return -EINVAL;
	steer = kzalloc(sizeof(*steer), GFP_KERNEL);
	if (!steer)
		return -ENOMEM;
	if (copy_from_user(steer->e, arg + 8, n * sizeof(steer->e[0]))) {
		kfree(steer);
		return -EFAULT;
	}
	for (i = 0; i < n; i++)
		if (steer->e[i].len > sizeof(steer->e[i].value)) {
			kfree(steer);
			return -EINVAL;
		}
	spin_lock_init(&steer->lock);
	steer->n = n;
	spin_lock_irqsave(&kcov->lock, flags);
	old = kcov->steer;
	kcov->steer = steer;
	spin_unlock_irqrestore(&kcov->lock, flags);
	kfree(old);
	return 0;
}

/* LEANUX: { u32 remaining; u32 mismatches; } */
static long kcov_steer_status(struct kcov *kcov, void __user *arg)
{
	u32 status[2] = { 0, 0 };
	unsigned long flags;

	spin_lock_irqsave(&kcov->lock, flags);
	if (kcov->steer) {
		spin_lock(&kcov->steer->lock);
		status[0] = kcov->steer->n - kcov->steer->head;
		status[1] = kcov->steer->mismatches;
		spin_unlock(&kcov->steer->lock);
	}
	spin_unlock_irqrestore(&kcov->lock, flags);
	return copy_to_user(arg, status, sizeof(status)) ? -EFAULT : 0;
}
"""
wr('kernel/kcov.c', s2)
sub('include/linux/kcov.h', 'u64 kcov_common_handle(void);\n', 'u64 kcov_common_handle(void);\n/* LEANUX: a choice recorded at a generic interception point. */\nvoid kcov_choice_ip(u32 kind, unsigned long ip, void *data, unsigned int len);\n')
sub('include/linux/kcov.h', 'static inline u64 kcov_common_handle(void)', 'static inline void kcov_choice_ip(u32 kind, unsigned long ip, void *data, unsigned int len) {}\nstatic inline u64 kcov_common_handle(void)')
R='drivers/char/random.c'
sub(R, '#include <asm/irq_regs.h>\n', '#include <asm/irq_regs.h>\n#include <linux/kcov.h>\n')
sub(R, '''void get_random_bytes(void *buf, size_t len)
{
	_get_random_bytes(buf, len);
}''', '''void get_random_bytes(void *buf, size_t len)
{
	_get_random_bytes(buf, len);
	kcov_choice_ip(1, _RET_IP_, buf, len);	/* LEANUX: a recorded choice */
}''')
sub(R, 'type get_random_ ##type(void)\t\t\t\t\t\t\t\\\n{\t\t\t\t\t\t\t\t\t\t\\\n\ttype ret;', 'static type __get_random_ ##type## _raw(void)\t\t\t\t\t\\\n{\t\t\t\t\t\t\t\t\t\t\\\n\ttype ret;')
sub(R, '''	local_unlock_irqrestore(&batched_entropy_ ##type.lock, flags);		\\
	return ret;								\\
}										\\
EXPORT_SYMBOL(get_random_ ##type);''', '''	local_unlock_irqrestore(&batched_entropy_ ##type.lock, flags);		\\
	return ret;								\\
}										\\
										\\
/* LEANUX: the exported draw records the choice; internal draws use _raw. */	\\
type get_random_ ##type(void)							\\
{										\\
	type ret = __get_random_ ##type## _raw();				\\
										\\
	kcov_choice_ip(100 + sizeof(ret), _RET_IP_, &ret, sizeof(ret));		\\
	return ret;								\\
}										\\
EXPORT_SYMBOL(get_random_ ##type);''')
sub(R, '''	u32 rand = get_random_u32();
	u64 mult;''', '''	u32 rand = __get_random_u32_raw();	/* LEANUX: recorded once, below */
	u64 mult;''')
sub(R, '''	if (unlikely(!ceil))
		return rand;

	mult = (u64)ceil * rand;
	if (unlikely((u32)mult < ceil)) {
		u32 bound = -ceil % ceil;
		while (unlikely((u32)mult < bound))
			mult = (u64)ceil * get_random_u32();
	}
	return mult >> 32;''', '''	if (unlikely(!ceil)) {
		kcov_choice_ip(110, _RET_IP_, &rand, sizeof(rand));
		return rand;
	}

	mult = (u64)ceil * rand;
	if (unlikely((u32)mult < ceil)) {
		u32 bound = -ceil % ceil;
		while (unlikely((u32)mult < bound))
			mult = (u64)ceil * __get_random_u32_raw();
	}
	rand = mult >> 32;
	kcov_choice_ip(110, _RET_IP_, &rand, sizeof(rand));
	return rand;''')
T='kernel/time/timekeeping.c'
s = rd(T)
s = s.replace('#include <linux/audit.h>\n', '#include <linux/audit.h>\n#include <linux/kcov.h>\n', 1)
readers = [
 ('u64 notrace ktime_get_mono_fast_ns(void)', 'EXPORT_SYMBOL_GPL(ktime_get_mono_fast_ns);'),
 ('u64 notrace ktime_get_raw_fast_ns(void)', 'EXPORT_SYMBOL_GPL(ktime_get_raw_fast_ns);'),
 ('u64 notrace ktime_get_boot_fast_ns(void)', 'EXPORT_SYMBOL_GPL(ktime_get_boot_fast_ns);'),
 ('u64 notrace ktime_get_tai_fast_ns(void)', 'EXPORT_SYMBOL_GPL(ktime_get_tai_fast_ns);'),
 ('u64 ktime_get_real_fast_ns(void)', 'EXPORT_SYMBOL_GPL(ktime_get_real_fast_ns);'),
 ('void ktime_get_real_ts64(struct timespec64 *ts)', 'EXPORT_SYMBOL(ktime_get_real_ts64);'),
 ('ktime_t ktime_get(void)', 'EXPORT_SYMBOL_GPL(ktime_get);'),
 ('ktime_t ktime_get_with_offset(enum tk_offsets offs)', 'EXPORT_SYMBOL_GPL(ktime_get_with_offset);'),
 ('ktime_t ktime_get_coarse_with_offset(enum tk_offsets offs)', 'EXPORT_SYMBOL_GPL(ktime_get_coarse_with_offset);'),
 ('ktime_t ktime_get_raw(void)', 'EXPORT_SYMBOL_GPL(ktime_get_raw);'),
 ('void ktime_get_ts64(struct timespec64 *ts)', 'EXPORT_SYMBOL_GPL(ktime_get_ts64);'),
 ('time64_t ktime_get_seconds(void)', 'EXPORT_SYMBOL_GPL(ktime_get_seconds);'),
 ('time64_t ktime_get_real_seconds(void)', 'EXPORT_SYMBOL_GPL(ktime_get_real_seconds);'),
 ('void ktime_get_raw_ts64(struct timespec64 *ts)', 'EXPORT_SYMBOL(ktime_get_raw_ts64);'),
 ('void getboottime64(struct timespec64 *ts)', 'EXPORT_SYMBOL_GPL(getboottime64);'),
 ('void ktime_get_coarse_real_ts64(struct timespec64 *ts)', 'EXPORT_SYMBOL(ktime_get_coarse_real_ts64);'),
 ('void ktime_get_coarse_ts64(struct timespec64 *ts)', 'EXPORT_SYMBOL(ktime_get_coarse_ts64);'),
]
for kind, (sig, exp) in enumerate(readers, start=200):
    m = re.match(r'(.*?)\b(\w+)\((.*)\)$', sig)
    prefix, name, args = m.group(1), m.group(2), m.group(3)
    ret = prefix.replace('notrace', '').strip()
    notrace = 'notrace ' if 'notrace' in prefix else ''
    assert s.count('\n' + sig + '\n') == 1, sig
    s = s.replace('\n' + sig + '\n', f'\nstatic __always_inline {ret} {notrace}leanux_raw_{name}({args})\n', 1)
    argname = '' if args == 'void' else args.split()[-1].lstrip('*')
    if ret == 'void':
        wrapper = (f'/* LEANUX: a recorded choice (a clock read). */\n{sig}\n{{\n\tleanux_raw_{name}({argname});\n'
                   f'\tkcov_choice_ip({kind}, _RET_IP_, ts, sizeof(*ts));\n}}\n')
    else:
        wrapper = (f'/* LEANUX: a recorded choice (a clock read). */\n{sig}\n{{\n\t{ret} v = leanux_raw_{name}({argname});\n\n'
                   f'\tkcov_choice_ip({kind}, _RET_IP_, &v, sizeof(v));\n\treturn v;\n}}\n')
    assert s.count('\n' + exp + '\n') == 1, exp
    s = s.replace('\n' + exp + '\n', '\n' + wrapper + exp + '\n', 1)
# the boot and TAI fast readers call the mono fast reader internally: the
# raw variant, so one call records once
for name in ('ktime_get_boot_fast_ns', 'ktime_get_tai_fast_ns'):
    i = s.index(f'leanux_raw_{name}(void)')
    j = s.index('\n}\n', i)
    body = s[i:j]
    assert body.count('ktime_get_mono_fast_ns()') == 1, name
    s = s[:i] + body.replace('ktime_get_mono_fast_ns()', 'leanux_raw_ktime_get_mono_fast_ns()') + s[j:]
wr(T, s)
# ---- D1 stream A: dispatch sections (choice-stream strategy, sections 4.3-4.4) ----
s = rd('kernel/kcov.c').rstrip('\n') + r'''

/*
 * LEANUX dispatch sections (choice-stream strategy, sections 4.3-4.4): the
 * deferred units of a trace are collected by dispatch, not per call site.
 * The guest's parent arms its remote KCOV instance with the dispatch set
 * (KCOV_LEANUX_DISPATCH_LOAD: function addresses the host resolved from
 * vmlinux). While it is armed, process_one_work opens a remote section under
 * the instance's common handle iff the work function is in the set, and the
 * NET_RX vector in handle_softirqs does the same iff net_rx_action is. Each
 * section writes a start record (kind 300: the function's address, then the
 * dispatched unit: the work item's address from process_one_work, the
 * timer's from call_timer_fn, 0 for a softirq; docs/2026-10-11-dispatch-order.md)
 * and a stop record (kind 301, the number of records dropped in the section),
 * sequence-numbered like every other record. KCOV's nesting rules hold: no
 * section in a task that already collects, and only a softirq section inside
 * a task section. A section that cannot open (unregistered handle, no area,
 * a nesting violation) or that loses records increments a counter, which
 * the parent reads back (KCOV_LEANUX_SECTION_STATUS) and fails on.
 */
#define KCOV_DISPATCH_MAX 16
static struct {
	u64 handle;
	u32 n;
	unsigned long funcs[KCOV_DISPATCH_MAX];
} kcov_dispatch;				/* under kcov_remote_lock */
static struct kcov *kcov_dispatch_kcov;		/* the armed instance, or NULL */
static atomic_t kcov_sections_dropped, kcov_sections_opened;

/* Whether the current section's area has no room left (PCs may be lost). */
static bool notrace kcov_section_area_full(struct task_struct *t)
{
	u64 *area = t->kcov_area;

	if (t->kcov_mode == KCOV_MODE_TRACE_PC)
		return READ_ONCE(area[0]) + 1 >= t->kcov_size;
	return 1 + (READ_ONCE(area[0]) + 1) * KCOV_WORDS_PER_CMP > t->kcov_size;
}

/* Whether kcov_remote_stop's move fits the instance's area in full. */
static bool notrace kcov_section_move_fits(struct task_struct *t)
{
	struct kcov *kcov = t->kcov;
	u64 dst = READ_ONCE(*(u64 *)kcov->area), src = READ_ONCE(*(u64 *)t->kcov_area);

	if (kcov->mode == KCOV_MODE_TRACE_PC)
		return dst + src <= kcov->size - 1;
	return dst + src <= (kcov->size - 1) / KCOV_WORDS_PER_CMP;
}

void notrace kcov_dispatch_start(struct kcov_dispatch_section *s, void *func, void *unit)
{
	struct task_struct *t = current;
	struct kcov *kcov;
	unsigned long flags, ip = (unsigned long)func;
	u64 v[2];
	bool member = false;
	u64 handle;
	u32 i;

	s->open = false;
	if (!READ_ONCE(kcov_dispatch_kcov))
		return;
	spin_lock_irqsave(&kcov_remote_lock, flags);
	kcov = kcov_dispatch_kcov;
	for (i = 0; kcov && i < kcov_dispatch.n; i++)
		if (kcov_dispatch.funcs[i] == ip)
			member = true;
	handle = kcov_dispatch.handle;
	spin_unlock_irqrestore(&kcov_remote_lock, flags);
	if (!member)
		return;
	if (in_task() ? kcov_mode_enabled(READ_ONCE(t->kcov_mode)) : !in_softirq_really() || t->kcov_softirq) {
		atomic_inc(&kcov_sections_dropped);	/* would nest */
		return;
	}
	s->saved_dropped = t->kcov_leanux_dropped;
	t->kcov_leanux_dropped = 0;
	kcov_remote_start(handle);
	if (in_task() ? !kcov_mode_enabled(READ_ONCE(t->kcov_mode)) || t->kcov != kcov : !t->kcov_softirq) {
		t->kcov_leanux_dropped = s->saved_dropped;
		atomic_inc(&kcov_sections_dropped);	/* not opened */
		return;
	}
	atomic_inc(&kcov_sections_opened);
	s->open = true;
	if (in_task())
		t->kcov_leanux_section = 1;
	v[0] = ip;
	v[1] = (unsigned long)unit;	/* the dispatched unit (dispatch order) */
	kcov_choice_write(t, 300, _RET_IP_, v, sizeof(v));
}
EXPORT_SYMBOL(kcov_dispatch_start);

void notrace kcov_dispatch_stop(struct kcov_dispatch_section *s)
{
	struct task_struct *t = current;
	u64 dropped;

	if (!s->open)
		return;
	if (kcov_section_area_full(t))
		t->kcov_leanux_dropped++;
	dropped = t->kcov_leanux_dropped;
	kcov_choice_write(t, 301, _RET_IP_, &dropped, sizeof(dropped));
	if (t->kcov_leanux_dropped || !kcov_section_move_fits(t))
		atomic_inc(&kcov_sections_dropped);
	kcov_remote_stop();
	t->kcov_leanux_dropped = s->saved_dropped;
	if (in_task())
		t->kcov_leanux_section = 0;
}
EXPORT_SYMBOL(kcov_dispatch_stop);

/*
 * LEANUX: a scheduling choice (D1 integration). On this CONFIG_PREEMPT_NONE
 * kernel a task section's worker gives up the CPU at a cond_resched; when
 * __cond_resched is about to schedule, it writes a resched record (kind 302,
 * the caller's return address, a zero word), so the trace records each
 * switch, including one to a task without a section. Only inside a task's
 * dispatch section: other tasks' reschedules are not choices of the trace.
 */
void notrace kcov_dispatch_resched(unsigned long ip)
{
	struct task_struct *t = current;
	u64 zero = 0;

	if (in_task() && t->kcov_leanux_section)
		kcov_choice_write(t, 302, ip, &zero, sizeof(zero));
}
EXPORT_SYMBOL(kcov_dispatch_resched);

/* LEANUX: arm: { u32 n; u32 pad; u64 funcs[n]; }, on the remote instance of
 * the calling task, under its common handle; disarmed in kcov_remote_reset. */
static long kcov_dispatch_load(struct kcov *kcov, void __user *arg)
{
	u64 funcs[KCOV_DISPATCH_MAX];
	unsigned long flags;
	long ret = 0;
	u32 n, i;

	if (get_user(n, (u32 __user *)arg))
		return -EFAULT;
	if (!n || n > KCOV_DISPATCH_MAX)
		return -EINVAL;
	if (copy_from_user(funcs, arg + 8, n * sizeof(funcs[0])))
		return -EFAULT;
	spin_lock_irqsave(&kcov->lock, flags);
	if (!kcov->remote || current->kcov != kcov || !current->kcov_handle) {
		spin_unlock_irqrestore(&kcov->lock, flags);
		return -EINVAL;
	}
	spin_lock(&kcov_remote_lock);
	if (kcov_dispatch_kcov) {
		ret = -EBUSY;
	} else {
		kcov_dispatch.handle = current->kcov_handle;
		kcov_dispatch.n = n;
		for (i = 0; i < n; i++)
			kcov_dispatch.funcs[i] = funcs[i];
		atomic_set(&kcov_sections_dropped, 0);
		atomic_set(&kcov_sections_opened, 0);
		kcov_dispatch_kcov = kcov;
	}
	spin_unlock(&kcov_remote_lock);
	spin_unlock_irqrestore(&kcov->lock, flags);
	return ret;
}

/* LEANUX: { u32 dropped; u32 opened; } since the instance was armed */
static long kcov_section_status(struct kcov *kcov, void __user *arg)
{
	u32 status[2];
	unsigned long flags;

	spin_lock_irqsave(&kcov_remote_lock, flags);
	if (kcov_dispatch_kcov != kcov) {
		spin_unlock_irqrestore(&kcov_remote_lock, flags);
		return -EINVAL;
	}
	status[0] = atomic_read(&kcov_sections_dropped);
	status[1] = atomic_read(&kcov_sections_opened);
	spin_unlock_irqrestore(&kcov_remote_lock, flags);
	return copy_to_user(arg, status, sizeof(status)) ? -EFAULT : 0;
}
'''
wr('kernel/kcov.c', s)
sub('kernel/kcov.c', """		if (pos + 3 + nwords >= size) {
			WRITE_ONCE(area[0], size - 1);
			return;
		}""", """		if (pos + 3 + nwords >= size) {
			WRITE_ONCE(area[0], size - 1);
			t->kcov_leanux_dropped++;
			return;
		}""")
sub('kernel/kcov.c', """		    size * sizeof(unsigned long)) {
			WRITE_ONCE(area[0], (size - 1) / KCOV_WORDS_PER_CMP);
			return;
		}""", """		    size * sizeof(unsigned long)) {
			WRITE_ONCE(area[0], (size - 1) / KCOV_WORDS_PER_CMP);
			t->kcov_leanux_dropped++;
			return;
		}""")
# kcov_mode_enabled is defined further down; the dispatch code sits at the end
sub('kernel/kcov.c', """	t->kcov_softirq = 0;
	t->kcov_saved_mode = 0;""", """	t->kcov_softirq = 0;
	t->kcov_leanux_dropped = 0;
	t->kcov_saved_mode = 0;""")
sub('kernel/kcov.c', """		hash_del(&remote->hnode);
		kfree(remote);
	}
	/* Do reset before unlock to prevent races with kcov_remote_start(). */""", """		hash_del(&remote->hnode);
		kfree(remote);
	}
	if (kcov_dispatch_kcov == kcov)
		kcov_dispatch_kcov = NULL;	/* LEANUX: disarm with the handles */
	/* Do reset before unlock to prevent races with kcov_remote_start(). */""")
sub('kernel/kcov.c', """static long kcov_steer_load(struct kcov *kcov, void __user *arg);
static long kcov_steer_status(struct kcov *kcov, void __user *arg);
""", """static long kcov_steer_load(struct kcov *kcov, void __user *arg);
static long kcov_steer_status(struct kcov *kcov, void __user *arg);
#define KCOV_LEANUX_DISPATCH_LOAD	_IOW('c', 202, unsigned long)
#define KCOV_LEANUX_SECTION_STATUS	_IOR('c', 203, unsigned long)
static long kcov_dispatch_load(struct kcov *kcov, void __user *arg);
static long kcov_section_status(struct kcov *kcov, void __user *arg);
""")
sub('kernel/kcov.c', """	case KCOV_LEANUX_STEER_STATUS:
		return kcov_steer_status(kcov, (void __user *)arg);
""", """	case KCOV_LEANUX_STEER_STATUS:
		return kcov_steer_status(kcov, (void __user *)arg);
	case KCOV_LEANUX_DISPATCH_LOAD:
		return kcov_dispatch_load(kcov, (void __user *)arg);
	case KCOV_LEANUX_SECTION_STATUS:
		return kcov_section_status(kcov, (void __user *)arg);
""")
# the dispatch-set state is used in kcov_remote_reset, above its definition
sub('kernel/kcov.c', """static DEFINE_SPINLOCK(kcov_remote_lock);
""", """static DEFINE_SPINLOCK(kcov_remote_lock);
static struct kcov *kcov_dispatch_kcov;		/* LEANUX: see kcov_dispatch_start */
""")
s = rd('kernel/kcov.c')
assert s.count('static struct kcov *kcov_dispatch_kcov;\t\t/* the armed instance, or NULL */\n') == 1
wr('kernel/kcov.c', s.replace('static struct kcov *kcov_dispatch_kcov;\t\t/* the armed instance, or NULL */\n', ''))
sub('include/linux/kcov.h', 'void kcov_choice_ip(u32 kind, unsigned long ip, void *data, unsigned int len);\n',
    'void kcov_choice_ip(u32 kind, unsigned long ip, void *data, unsigned int len);\n'
    '/* LEANUX: a dispatch section (process_one_work, the NET_RX vector). */\n'
    'struct kcov_dispatch_section { bool open; unsigned int saved_dropped; };\n'
    'void kcov_dispatch_start(struct kcov_dispatch_section *s, void *func, void *unit);\n'
    'void kcov_dispatch_stop(struct kcov_dispatch_section *s);\n'
    '/* LEANUX: __cond_resched is about to schedule. */\n'
    'void kcov_dispatch_resched(unsigned long ip);\n')
sub('include/linux/kcov.h', 'static inline void kcov_choice_ip(u32 kind, unsigned long ip, void *data, unsigned int len) {}\n',
    'static inline void kcov_choice_ip(u32 kind, unsigned long ip, void *data, unsigned int len) {}\n'
    'struct kcov_dispatch_section { bool open; };\n'
    'static inline void kcov_dispatch_start(struct kcov_dispatch_section *s, void *func, void *unit) {}\n'
    'static inline void kcov_dispatch_stop(struct kcov_dispatch_section *s) {}\n'
    'static inline void kcov_dispatch_resched(unsigned long ip) {}\n')
sub('include/linux/sched.h', """	/* Collect coverage from softirq context: */
	unsigned int			kcov_softirq;
""", """	/* Collect coverage from softirq context: */
	unsigned int			kcov_softirq;

	/* LEANUX: records dropped in the current dispatch section: */
	unsigned int			kcov_leanux_dropped;

	/* LEANUX: whether the task is in a dispatch section: */
	unsigned int			kcov_leanux_section;
""")
W = 'kernel/workqueue.c'
sub(W, '#include <linux/irq_work.h>\n', '#include <linux/irq_work.h>\n#include <linux/kcov.h>\n')
sub(W, """	int lockdep_start_depth, rcu_start_depth;
	bool bh_draining = pool->flags & POOL_BH_DRAINING;
""", """	int lockdep_start_depth, rcu_start_depth;
	bool bh_draining = pool->flags & POOL_BH_DRAINING;
	struct kcov_dispatch_section section;	/* LEANUX */
""")
sub(W, """	trace_workqueue_execute_start(work);
	worker->current_func(work);
""", """	trace_workqueue_execute_start(work);
	kcov_dispatch_start(&section, worker->current_func, work);	/* LEANUX */
	worker->current_func(work);
	kcov_dispatch_stop(&section);
""")
# dispatch order (docs/2026-10-11-dispatch-order.md): the queue record, at
# the one point every queued work item passes (queue_work_on, queue_work_node,
# a delayed work's timer, flush_delayed_work), once its pending bit is set
sub(W, """	trace_workqueue_queue_work(req_cpu, pwq, work);
""", """	trace_workqueue_queue_work(req_cpu, pwq, work);
	kcov_work_queued(work, _RET_IP_);	/* LEANUX: the queue record (kind 307) */
""")
S = 'kernel/softirq.c'
sub(S, '#include <linux/workqueue.h>\n', '#include <linux/workqueue.h>\n#include <linux/kcov.h>\n')
sub(S, """	struct softirq_action *h;
	bool in_hardirq;
	__u32 pending;
	int softirq_bit;
""", """	struct softirq_action *h;
	bool in_hardirq;
	__u32 pending;
	int softirq_bit;
	struct kcov_dispatch_section section;	/* LEANUX */
""")
sub(S, """		trace_softirq_entry(vec_nr);
		h->action();
""", """		trace_softirq_entry(vec_nr);
		/* LEANUX: the NET_RX vector only (choice-stream strategy, 4.3) */
		section.open = false;
		if (vec_nr == NET_RX_SOFTIRQ)
			kcov_dispatch_start(&section, h->action, NULL);
		h->action();
		kcov_dispatch_stop(&section);
""")
sub('kernel/sched/core.c', """	if (should_resched(0) && !irqs_disabled()) {
		preempt_schedule_common();
		return 1;
	}
""", """	if (should_resched(0) && !irqs_disabled()) {
		kcov_dispatch_resched(_RET_IP_);	/* LEANUX */
		preempt_schedule_common();
		return 1;
	}
""")
# ---- D3 stream K: timers and time control (docs/2026-10-05-d3-timers.md) ----
sub('kernel/kcov.c', '#include <linux/refcount.h>\n', '#include <linux/refcount.h>\n#include <linux/workqueue.h>\t/* LEANUX: kcov_work_queued */\n')
s = rd('kernel/kcov.c').rstrip('\n') + r"""

/*
 * LEANUX D3 (docs/2026-10-05-d3-timers.md, section 3.3): the arm record.
 * mod_timer calls this with the timer's function, jiffies and the new
 * expiry; for a function in the armed dispatch set, in a recording context,
 * it writes kind 303 {jiffies, expires, timer} (24 bytes: the timer's
 * address names the unit its dispatch section starts with, dispatch
 * order) at the caller's return address. Lock-free: mod_timer is hot across the kernel, and the set only
 * changes while no trace runs (kcov_dispatch_load before the trace process
 * exists, disarm in kcov_remote_reset), so a READ_ONCE snapshot suffices;
 * outside a trace this costs one load. Written only when the instance was
 * armed with KCOV_DISPATCH_ARM_RECORDS (a load-time switch: off until the
 * mirror consumes the record).
 */
void notrace kcov_timer_arm(void *func, unsigned long now, unsigned long expires, unsigned long ip, void *timer)
{
	unsigned long fn = (unsigned long)func;
	u64 v[3];
	u32 n, i;

	if (!READ_ONCE(kcov_dispatch_kcov) || !(READ_ONCE(kcov_dispatch.flags) & KCOV_DISPATCH_ARM_RECORDS))
		return;
	n = min_t(u32, READ_ONCE(kcov_dispatch.n), KCOV_DISPATCH_MAX);
	for (i = 0; i < n; i++)
		if (READ_ONCE(kcov_dispatch.funcs[i]) == fn) {
			v[0] = now;
			v[1] = expires;
			v[2] = (unsigned long)timer;
			kcov_choice_ip(303, ip, v, sizeof(v));
			return;
		}
}
EXPORT_SYMBOL(kcov_timer_arm);

/*
 * LEANUX dispatch order (docs/2026-10-11-dispatch-order.md): the queue
 * record. __queue_work calls this for every work item it queues; for a work
 * function in the armed dispatch set, in a recording context, it writes
 * kind 307 {work, func} (16 bytes) at the caller's return address, gated
 * like the arm record (KCOV_DISPATCH_ARM_RECORDS). The item's dispatch
 * carries the same address in its kind-300 start record, so the order in
 * which queued units run is recorded, never assumed. Lock-free like
 * kcov_timer_arm; outside a trace one load.
 */
void notrace kcov_work_queued(struct work_struct *work, unsigned long ip)
{
	unsigned long fn = (unsigned long)work->func;
	u64 v[2];
	u32 n, i;

	if (!READ_ONCE(kcov_dispatch_kcov) || !(READ_ONCE(kcov_dispatch.flags) & KCOV_DISPATCH_ARM_RECORDS))
		return;
	n = min_t(u32, READ_ONCE(kcov_dispatch.n), KCOV_DISPATCH_MAX);
	for (i = 0; i < n; i++)
		if (READ_ONCE(kcov_dispatch.funcs[i]) == fn) {
			v[0] = (unsigned long)work;
			v[1] = fn;
			kcov_choice_ip(307, ip, v, sizeof(v));
			return;
		}
}
EXPORT_SYMBOL(kcov_work_queued);

/*
 * LEANUX W9 (docs/2026-10-06-w8-w9-netns-routing.md, section 4.1): the
 * jiffies value the dst cache stores, at a reset (dst_cache_reset, the
 * inline in include/net/dst_cache.h: dst_cache_init, dst_cache_reset_now and
 * WireGuard's socket.c callers) and at the refresh of a miss
 * (dst_cache_per_cpu_get's fail label). The cache's hit test is
 * time_after(refresh_ts, reset_ts): a plain jiffies comparison the mirror
 * cannot otherwise compute. Kind 306, 8 bytes, at the site's own address
 * (_THIS_IP_: the record resolves through the inline chain to the header
 * line). Gated like the arm record (KCOV_DISPATCH_ARM_RECORDS); outside a
 * trace one load. Record-only: the stored value is the one recorded.
 */
void notrace kcov_dst_cache_ts(unsigned long ts, unsigned long ip)
{
	u64 v = ts;

	if (!READ_ONCE(kcov_dispatch_kcov) || !(READ_ONCE(kcov_dispatch.flags) & KCOV_DISPATCH_ARM_RECORDS))
		return;
	kcov_choice_ip(306, ip, &v, sizeof(v));
}
EXPORT_SYMBOL(kcov_dst_cache_ts);

/*
 * LEANUX epoll (docs/2026-10-12-epoll-design.md, section 3.2): the address
 * of the struct file an epoll item is keyed by (ep_cmp_ffd: the file
 * pointer, then the fd), recorded at ep_rbtree_insert (fs/eventpoll.c,
 * _THIS_IP_) once per successful EPOLL_CTL_ADD, kind 308, 8 bytes. Slab
 * placement is a hidden input: it fixes the walk order of the set's tree
 * (ep_clear_and_put's two walks, ep_loop_check_proc), so the mirror orders
 * its items by the recorded address instead of assuming allocation order.
 * Written in any recording context, like the random and clock records: an
 * FS trace loads no dispatch set, so the KCOV_DISPATCH_ARM_RECORDS gate of
 * the arm, queue and dst-cache records is not available to it; outside a
 * trace kcov_choice_ip returns at its mode check. Record-only: nothing the
 * value decides changes.
 */
void notrace kcov_epoll_insert(unsigned long file, unsigned long ip)
{
	u64 v = file;

	kcov_choice_ip(308, ip, &v, sizeof(v));
}
EXPORT_SYMBOL(kcov_epoll_insert);

/*
 * LEANUX seccomp (docs/2026-10-12-seccomp-design.md, section 3.3): the eBPF
 * program bpf_convert_filter's second pass wrote for a classic filter, as
 * data: one kind-309 record with the eBPF length, then one kind-309 record
 * per bpf_insn, all 8 bytes, from bpf_migrate_filter's one call site
 * (net/core/filter.c, _THIS_IP_), before bpf_prog_select_runtime locks the
 * pages. A choice record carries at most KCOV_CHOICE_MAX_WORDS payload
 * words, so the program is recorded per instruction; one site and one
 * record width, since the check keys a site by its consumer frame and one
 * length. The mirror checks the length, then its own translation in order,
 * so a mismatch names the first differing instruction. Written in any
 * recording context, like the kind-308 record. Record-only: nothing the
 * values decide changes.
 */
void notrace kcov_seccomp_program(const void *insns, unsigned int len, unsigned long ip)
{
	const u64 *words = insns;
	u64 v = len;
	unsigned int i;

	kcov_choice_ip(309, ip, &v, sizeof(v));
	for (i = 0; i < len; i++) {
		v = words[i];
		kcov_choice_ip(309, ip, &v, sizeof(v));
	}
}
EXPORT_SYMBOL(kcov_seccomp_program);

/*
 * LEANUX D3 (section 4.3): the virtual time advance, on the calling task's
 * own KCOV descriptor: { unsigned long ticks; }, 1 <= ticks <= 2^31. Only
 * from a task that is collecting (the trace process), so the kind-304
 * record {jiffies before, jiffies after} is never lost; the helper refuses
 * any timekeeper clocksource but refined-jiffies (-EOPNOTSUPP). The next
 * tick advances the timekeeper and raises TIMER_SOFTIRQ, as when time passes.
 * Interrupts stay disabled from the jump until the kind-304 record is
 * written: a tick in between would run the timers the jump made due (at its
 * irq exit) before the record, so their records would precede it.
 */
static long kcov_time_advance(unsigned long __user *arg)
{
	struct task_struct *t = current;
	unsigned long ticks, flags;
	u64 v[2];
	int ret;

	if (get_user(ticks, arg))
		return -EFAULT;
	if (!ticks || ticks > (1UL << 31))
		return -EINVAL;
	if (!check_kcov_mode(KCOV_MODE_TRACE_PC, t) &&
	    !(IS_ENABLED(CONFIG_KCOV_ENABLE_COMPARISONS) && check_kcov_mode(KCOV_MODE_TRACE_CMP, t)))
		return -EPERM;
	local_irq_save(flags);
	ret = leanux_time_advance(ticks, &v[0], &v[1]);
	if (!ret)
		kcov_choice_write(t, 304, _RET_IP_, v, sizeof(v));
	local_irq_restore(flags);
	return ret;
}

/*
 * LEANUX review item 7 (docs/2026-10-13-review-items-7-8.md, section 5): the
 * end of a guest wait as a record. KCOV_LEANUX_JIFFIES reads jiffies_64 and
 * appends kind 310 {jiffies} (8 bytes) to the REMOTE area of this process's
 * common handle, where the waits' timer sections already land (the task's
 * own window closed at the operation's return), under the remote kcov's lock
 * like kcov_remote_stop's move; jiffies is read inside that critical section,
 * so no tick separates the value from the record's sequence number. The
 * remote kcov is looked up under kcov_remote_lock and held by a reference
 * across its own lock (kcov_remote_enable nests the locks the other way).
 * No remote coverage enabled: -ENOENT, so the guest fails noisily rather
 * than the mirror missing a record silently. Record-only.
 */
static long kcov_jiffies_read(unsigned long __user *arg)
{
	struct task_struct *t = current;
	struct kcov_remote *remote;
	struct kcov *kcov = NULL;
	unsigned long flags;
	u64 j;
	int written = 0;

	spin_lock_irqsave(&kcov_remote_lock, flags);
	remote = kcov_remote_find(t->kcov_handle);
	if (remote) {
		kcov = remote->kcov;
		kcov_get(kcov);
	}
	spin_unlock_irqrestore(&kcov_remote_lock, flags);
	if (!kcov)
		return -ENOENT;
	spin_lock_irqsave(&kcov->lock, flags);
	j = get_jiffies_64();
	if (kcov->remote && kcov->area &&
	    (kcov->mode == KCOV_MODE_TRACE_PC || kcov->mode == KCOV_MODE_TRACE_CMP)) {
		kcov_choice_write_area(t, kcov->mode, (u64 *)kcov->area, kcov->size, 310, _RET_IP_, &j, sizeof(j));
		written = 1;
	}
	spin_unlock_irqrestore(&kcov->lock, flags);
	kcov_put(kcov);
	if (!written)
		return -ENOENT;
	if (put_user((unsigned long)j, arg))
		return -EFAULT;
	return 0;
}
"""
wr('kernel/kcov.c', s)
sub('kernel/kcov.c', """#define KCOV_DISPATCH_MAX 16
static struct {
	u64 handle;
	u32 n;
	unsigned long funcs[KCOV_DISPATCH_MAX];
} kcov_dispatch;				/* under kcov_remote_lock */""", """#define KCOV_DISPATCH_MAX 16
/* LEANUX D3: dispatch-load flags (the load argument's second word) */
#define KCOV_DISPATCH_ARM_RECORDS 1	/* write kind-303 arm records */
static struct {
	u64 handle;
	u32 n;
	u32 flags;
	unsigned long funcs[KCOV_DISPATCH_MAX];
} kcov_dispatch;				/* under kcov_remote_lock */""")
sub('kernel/kcov.c', """/* LEANUX: arm: { u32 n; u32 pad; u64 funcs[n]; }, on the remote instance of
 * the calling task, under its common handle; disarmed in kcov_remote_reset. */""", """/* LEANUX: arm: { u32 n; u32 flags; u64 funcs[n]; }, on the remote instance
 * of the calling task, under its common handle; disarmed in
 * kcov_remote_reset. flags: KCOV_DISPATCH_ARM_RECORDS (D3) or 0. */""")
sub('kernel/kcov.c', """	u64 funcs[KCOV_DISPATCH_MAX];
	unsigned long flags;
	long ret = 0;
	u32 n, i;

	if (get_user(n, (u32 __user *)arg))
		return -EFAULT;
	if (!n || n > KCOV_DISPATCH_MAX)
		return -EINVAL;""", """	u64 funcs[KCOV_DISPATCH_MAX];
	unsigned long flags;
	long ret = 0;
	u32 n, i, load_flags;

	if (get_user(n, (u32 __user *)arg) || get_user(load_flags, (u32 __user *)(arg + 4)))
		return -EFAULT;
	if (!n || n > KCOV_DISPATCH_MAX || (load_flags & ~KCOV_DISPATCH_ARM_RECORDS))
		return -EINVAL;""")
sub('kernel/kcov.c', """		kcov_dispatch.handle = current->kcov_handle;
		kcov_dispatch.n = n;""", """		kcov_dispatch.handle = current->kcov_handle;
		kcov_dispatch.n = n;
		kcov_dispatch.flags = load_flags;""")
sub('kernel/kcov.c', """static long kcov_dispatch_load(struct kcov *kcov, void __user *arg);
static long kcov_section_status(struct kcov *kcov, void __user *arg);
""", """static long kcov_dispatch_load(struct kcov *kcov, void __user *arg);
static long kcov_section_status(struct kcov *kcov, void __user *arg);
#define KCOV_LEANUX_TIME_ADVANCE	_IOW('c', 204, unsigned long)
static long kcov_time_advance(unsigned long __user *arg);
""")
# before kcov_ioctl's locked path, as the steering ioctls: no instance state
sub('kernel/kcov.c', """	case KCOV_LEANUX_DISPATCH_LOAD:
		return kcov_dispatch_load(kcov, (void __user *)arg);
""", """	case KCOV_LEANUX_DISPATCH_LOAD:
		return kcov_dispatch_load(kcov, (void __user *)arg);
	case KCOV_LEANUX_TIME_ADVANCE:
		return kcov_time_advance((unsigned long __user *)arg);
""")
sub('include/linux/kcov.h', """/* LEANUX: __cond_resched is about to schedule. */
void kcov_dispatch_resched(unsigned long ip);
""", """/* LEANUX: __cond_resched is about to schedule. */
void kcov_dispatch_resched(unsigned long ip);
/* LEANUX D3: mod_timer's arm record (kind 303). */
void kcov_timer_arm(void *func, unsigned long now, unsigned long expires, unsigned long ip, void *timer);
/* LEANUX dispatch order: __queue_work's queue record (kind 307). */
struct work_struct;
void kcov_work_queued(struct work_struct *work, unsigned long ip);
/* LEANUX epoll: ep_rbtree_insert's file-address record (kind 308). */
void kcov_epoll_insert(unsigned long file, unsigned long ip);
/* LEANUX seccomp: bpf_migrate_filter's translated-program records (kind 309). */
void kcov_seccomp_program(const void *insns, unsigned int len, unsigned long ip);
""")
sub('include/linux/kcov.h', """static inline void kcov_dispatch_resched(unsigned long ip) {}
""", """static inline void kcov_dispatch_resched(unsigned long ip) {}
static inline void kcov_timer_arm(void *func, unsigned long now, unsigned long expires, unsigned long ip, void *timer) {}
struct work_struct;
static inline void kcov_work_queued(struct work_struct *work, unsigned long ip) {}
static inline void kcov_epoll_insert(unsigned long file, unsigned long ip) {}
static inline void kcov_seccomp_program(const void *insns, unsigned int len, unsigned long ip) {}
""")
sub('include/linux/kcov.h', 'u64 kcov_common_handle(void);\n', 'u64 kcov_common_handle(void);\n'
    '/* LEANUX D3: the virtual time advance (kernel/time/timekeeping.c). */\n'
    'int leanux_time_advance(unsigned long ticks, u64 *before, u64 *after);\n')
s = rd(T).rstrip('\n') + r"""

/*
 * LEANUX D3 (docs/2026-10-05-d3-timers.md, section 4.3, option C-jiffies):
 * advance jiffies_64 by @ticks, as do_timer does at a tick, under
 * jiffies_lock and jiffies_seq; tick_next_period moves with it (cosmetic in
 * periodic mode). Nothing else: on the refined-jiffies timekeeper the next
 * tick's update_wall_time reads the jumped jiffies and moves every clock by
 * the same amount. On any other timekeeper the clocks would not follow, so
 * the helper fails closed with -EOPNOTSUPP. Holding timekeeper_lock keeps
 * the clocksource from changing in between (no path nests the two locks the
 * other way round).
 */
int leanux_time_advance(unsigned long ticks, u64 *before, u64 *after)
{
	struct timekeeper *tk = &tk_core.timekeeper;
	unsigned long flags;
	int ret = -EOPNOTSUPP;

	raw_spin_lock_irqsave(&timekeeper_lock, flags);
	if (tk->tkr_mono.clock && !strcmp(tk->tkr_mono.clock->name, "refined-jiffies")) {
		raw_spin_lock(&jiffies_lock);
		write_seqcount_begin(&jiffies_seq);
		*before = jiffies_64;
		tick_next_period = ktime_add_ns(tick_next_period, (u64)ticks * TICK_NSEC);
		do_timer(ticks);
		*after = jiffies_64;
		write_seqcount_end(&jiffies_seq);
		raw_spin_unlock(&jiffies_lock);
		ret = 0;
	}
	raw_spin_unlock_irqrestore(&timekeeper_lock, flags);
	return ret;
}
"""
wr(T, s)
TM = 'kernel/time/timer.c'
sub(TM, '#include <linux/random.h>\n', '#include <linux/random.h>\n#include <linux/kcov.h>\n')
sub(TM, """	int count = preempt_count();

#ifdef CONFIG_LOCKDEP
	/*
	 * It is permissible to free the timer from inside the""", """	int count = preempt_count();
	struct kcov_dispatch_section section;	/* LEANUX */

#ifdef CONFIG_LOCKDEP
	/*
	 * It is permissible to free the timer from inside the""")
sub(TM, """	trace_timer_expire_entry(timer, baseclk);
	fn(timer);
	trace_timer_expire_exit(timer);
""", """	trace_timer_expire_entry(timer, baseclk);
	/* LEANUX D3: a timer dispatch section iff fn is in the armed set */
	kcov_dispatch_start(&section, fn, timer);
	fn(timer);
	kcov_dispatch_stop(&section);
	trace_timer_expire_exit(timer);
""")
sub(TM, """int mod_timer(struct timer_list *timer, unsigned long expires)
{
	return __mod_timer(timer, expires, 0);
}""", """int mod_timer(struct timer_list *timer, unsigned long expires)
{
	/* LEANUX D3: the arm record (kind 303) for an armed function */
	kcov_timer_arm(timer->function, jiffies, expires, _RET_IP_, timer);
	return __mod_timer(timer, expires, 0);
}""")
# ---- W9: the dst cache's jiffies (docs/2026-10-06-w8-w9-netns-routing.md, 4.1) ----
# Record-only: the value stored is the value recorded; kind 306, two sites.
DC='include/net/dst_cache.h'
sub(DC, '''#include <linux/jiffies.h>
''', '''#include <linux/jiffies.h>
#include <linux/instruction_pointer.h>
''')
sub(DC, '''static inline void dst_cache_reset(struct dst_cache *dst_cache)
{
	WRITE_ONCE(dst_cache->reset_ts, jiffies);
}''', '''#ifdef CONFIG_KCOV
/* LEANUX W9: the jiffies the dst cache stores, recorded (kind 306). */
void kcov_dst_cache_ts(unsigned long ts, unsigned long ip);
#else
static inline void kcov_dst_cache_ts(unsigned long ts, unsigned long ip) {}
#endif

static inline void dst_cache_reset(struct dst_cache *dst_cache)
{
	unsigned long ts = jiffies;

	WRITE_ONCE(dst_cache->reset_ts, ts);
	kcov_dst_cache_ts(ts, _THIS_IP_);	/* LEANUX W9: kind 306 */
}''')
sub('net/core/dst_cache.c', '''fail:
	idst->refresh_ts = jiffies;
	return NULL;''', '''fail:
	idst->refresh_ts = jiffies;
	kcov_dst_cache_ts(idst->refresh_ts, _THIS_IP_);	/* LEANUX W9: kind 306 */
	return NULL;''')
# ---- epoll stream R: the tree's key order (docs/2026-10-12-epoll-design.md, 3.2) ----
# Record-only: the file address an item is keyed by, at its insertion; kind
# 308, one site. Line-preserving (stream T): no include, the declaration and
# the call share rb_insert_color_cached's line (fs/eventpoll.c:1585), so the
# patched file has the pristine line count and the checker's statement spans,
# read from the pristine tree, stay exact; the record's site is :1585.
EP='fs/eventpoll.c'
sub(EP, '''	rb_link_node(&epi->rbn, parent, p);
	rb_insert_color_cached(&epi->rbn, &ep->rbr, leftmost);
}''', '''	rb_link_node(&epi->rbn, parent, p);
	rb_insert_color_cached(&epi->rbn, &ep->rbr, leftmost); { extern void kcov_epoll_insert(unsigned long file, unsigned long ip); kcov_epoll_insert((unsigned long)epi->ffd.file, _THIS_IP_); }	/* LEANUX epoll: kind 308, line-preserving */
}''')
# ---- seccomp stream W: the translated program (docs/2026-10-12-seccomp-design.md, 3.3) ----
# Record-only: the eBPF length, then the instructions bpf_convert_filter's
# second pass wrote; kind 309, one site. Line-preserving: net/core/filter.c
# is an anchored file and the checker reads its statements from the pristine
# source while DWARF carries the built source's lines, so no include is
# added and the extern declaration and the call share the line of
# bpf_migrate_filter's `fp = bpf_prog_select_runtime(fp, &err);` (1315 in
# both sources); wc -l of the patched and pristine file agree.
FL='net/core/filter.c'
sub(FL, '''		goto out_err_free;

	fp = bpf_prog_select_runtime(fp, &err);''', '''		goto out_err_free;

	{ extern void kcov_seccomp_program(const void *insns, unsigned int len, unsigned long ip); kcov_seccomp_program(fp->insnsi, new_len, _THIS_IP_); } fp = bpf_prog_select_runtime(fp, &err);	/* LEANUX seccomp: kind 309 */''')
# ---- A stream K1: allocation outcomes (docs/2026-10-05-a-alloc.md, section 4) ----
# LEANUX_ALLOC_CONTROLS=1 generates the control kernel's patch instead
# (choice-stream-alloc-controls.patch; section 7, K1, K4, K5): load flags
# that make a forced failure record ok = 1 (K1), treat the steered
# encounter as __GFP_NOFAIL (K4), or name encounters by address only (K5).
# Never the oracle: the oracle's load rejects these flags.
CONTROLS = os.environ.get('LEANUX_ALLOC_CONTROLS') == '1'
ALLOC_CONTROL_TEXT = {
    '@@CONTROL_DOC@@': '' if not CONTROLS else '\n * CONTROL KERNEL (never the oracle): load flags 2 (a forced failure\n * records ok = 1), 4 (the steered encounter counts as __GFP_NOFAIL), 8\n * (the naming test is by address only).',
    '@@CONTROL_DEFS@@': '#define KCOV_ALLOC_CONTROLS 0\n' if not CONTROLS else
        '#define KCOV_ALLOC_CTL_RECORD_OK 2\t/* control K1 */\n#define KCOV_ALLOC_CTL_NOFAIL 4\t\t/* control K4 */\n'
        '#define KCOV_ALLOC_CTL_ADDR_NAMING 8\t/* control K5 */\n'
        '#define KCOV_ALLOC_CONTROLS (KCOV_ALLOC_CTL_RECORD_OK | KCOV_ALLOC_CTL_NOFAIL | KCOV_ALLOC_CTL_ADDR_NAMING)\n',
    '@@CONTROL_GFP@@': '' if not CONTROLS else '\tif (load_flags & KCOV_ALLOC_CTL_NOFAIL)\n\t\tgfp |= __GFP_NOFAIL;\n',
    '@@NAMING_CHAIN@@': 'use_chain' if not CONTROLS else 'use_chain && !(load_flags & KCOV_ALLOC_CTL_ADDR_NAMING)',
    '@@FORCED_OK@@': 'false' if not CONTROLS else '!!(flags & KCOV_ALLOC_CTL_RECORD_OK)',
}
s = rd('kernel/kcov.c').rstrip('\n') + r"""

/*
 * LEANUX A (docs/2026-10-05-a-alloc.md, section 4): allocation outcomes as
 * recorded choices. slab_alloc_node and __alloc_pages_noprof call
 * kcov_alloc_pre/kcov_alloc_post (include/linux/kcov.h) with the entry's
 * explicit return address; the bulk allocators are unhooked by construction.
 * The guest loads the allocation set (KCOV_LEANUX_ALLOC_LOAD, before any
 * trace work) on one KCOV instance; it is disarmed with that instance
 * (kcov_remote_reset). The hook, in this order: one load of
 * kcov_alloc_armed; the recording-context test; membership of the
 * canonicalized address in one of up to 64 sorted [lo, hi) ranges, or, with
 * n = 0 and KCOV_ALLOC_INVENTORY, every allocation (inventory pass 1, no
 * chain); then the record, kind 305, five words:
 *   word 0: bits 0-7 the outcome (1 ok, 0 NULL); bit 8 nested (a refill: an
 *           allocation inside another recorded one, in the same context);
 *           bit 9 the page allocator (the size field is the order); bit 10
 *           the unwind did not find the address on the stack; bits 11-31
 *           orig_size (slab, saturating) or order (page); bits 32-63 the gfp
 *           mask the hook saw (after gfp_allowed_mask; on the page path also
 *           after current_gfp_context);
 *   words 1-4: the return addresses above the address, innermost first,
 *           zero-padded (zero in inventory pass 1 and for nested records in
 *           inventory mode).
 * Lock-free like kcov_timer_arm: the set changes only while no trace work
 * runs, and a load clears kcov_alloc_armed before it writes the set. A
 * record that does not fit marks the area full (kcov_choice_write).
 * Forced failures (stream K2, section 5): the trace's steering schedule
 * decides them, kcov_steer_alloc below.@@CONTROL_DOC@@
 */
#define KCOV_ALLOC_RANGES_MAX 64
#define KCOV_ALLOC_INVENTORY 1		/* load flag: record every candidate */
@@CONTROL_DEFS@@#define KCOV_ALLOC_UNWIND 16		/* stack entries searched for the address */
#define KCOV_ALLOC_NESTED (1ULL << 8)
#define KCOV_ALLOC_PAGE (1ULL << 9)
#define KCOV_ALLOC_NOCHAIN (1ULL << 10)
#define KCOV_ALLOC_SIZE_MAX ((1ULL << 21) - 1)
struct kcov_alloc_range { u64 lo, hi; };
u32 kcov_alloc_armed;
static struct {
	u32 n;
	u32 flags;
	struct kcov_alloc_range r[KCOV_ALLOC_RANGES_MAX];
} kcov_alloc;
static atomic_t kcov_alloc_records, kcov_alloc_unwinds;
static atomic64_t kcov_alloc_unwind_cycles;
static DEFINE_PER_CPU(unsigned int, kcov_alloc_softirq_depth);

static notrace bool kcov_leanux_recording(struct task_struct *t)
{
	return check_kcov_mode(KCOV_MODE_TRACE_PC, t) ||
	       (IS_ENABLED(CONFIG_KCOV_ENABLE_COMPARISONS) && check_kcov_mode(KCOV_MODE_TRACE_CMP, t));
}

/* The depth of recorded allocations in progress in the current context: a
 * softirq that interrupts a task's allocation is not nested in it. */
static notrace unsigned int *kcov_alloc_depth(struct task_struct *t)
{
	return in_task() ? &t->kcov_leanux_in_alloc : this_cpu_ptr(&kcov_alloc_softirq_depth);
}

static notrace bool kcov_alloc_member(unsigned long ip, u32 n)
{
	u32 lo = 0, hi = n, mid;

	while (lo < hi) {
		mid = lo + (hi - lo) / 2;
		if (ip < READ_ONCE(kcov_alloc.r[mid].lo))
			hi = mid;
		else if (ip >= READ_ONCE(kcov_alloc.r[mid].hi))
			lo = mid + 1;
		else
			return true;
	}
	return false;
}

/* The return addresses above addr on the current stack (ORC). */
static noinline notrace void kcov_alloc_chain(unsigned long addr, u64 *w0, u64 *chain)
{
	unsigned long entries[KCOV_ALLOC_UNWIND];
	u64 start = get_cycles();
	unsigned int n, i, j;

	n = stack_trace_save(entries, KCOV_ALLOC_UNWIND, 0);
	for (i = 0; i < n && entries[i] != addr; i++)
		;
	if (i == n)
		*w0 |= KCOV_ALLOC_NOCHAIN;
	else
		for (j = 0; j < 4 && i + 1 + j < n; j++)
			chain[j] = canonicalize_ip(entries[i + 1 + j]);
	atomic_inc(&kcov_alloc_unwinds);
	atomic64_add(get_cycles() - start, &kcov_alloc_unwind_cycles);
}

static notrace void kcov_alloc_record(struct task_struct *t, struct kcov_alloc_ctx *ctx, bool ok, bool steered)
{
	u64 w[5] = { ctx->word0 | (ok ? 1 : 0), ctx->chain[0], ctx->chain[1], ctx->chain[2], ctx->chain[3] };

	kcov_choice_write(t, 305 | (steered ? 0x8000 : 0), ctx->addr, w, sizeof(w));
	atomic_inc(&kcov_alloc_records);
}

/*
 * LEANUX A stream K2 (section 5.2): steering an allocation. A kind-305
 * schedule entry names an encounter when one of its return addresses is the
 * allocation's address or, with KCOV_STEER_CHAIN, one of the unwound return
 * addresses above it (a helper site: the consumer's call into the helper).
 * Chain containment decides both whether the encounter is named at all and
 * whether it matches the head entry; an addr-only naming test would leave
 * helper sites silently unsteered (M4). Kind-305 entries are only ever
 * "draw" or "fail" (value 0, checked at load).
 */
static notrace bool kcov_steer_alloc_names(const struct kcov_steer_entry *e, unsigned long ip, const u64 *chain,
					   bool use_chain)
{
	u32 j, k;

	if (e->kind != 305)
		return false;
	for (j = 0; j < KCOV_STEER_IPS; j++) {
		if (!e->ips[j])
			continue;
		if (e->ips[j] == ip)
			return true;
		if (use_chain && (e->flags & KCOV_STEER_CHAIN))
			for (k = 0; k < 4; k++)
				if (chain[k] && e->ips[j] == chain[k])
					return true;
	}
	return false;
}

/* 1: fail this allocation; 0: not steered (no schedule, not named, a draw
 * entry, or a __GFP_NOFAIL allocation, whose entry stays: never forced, M2);
 * -1: a named encounter that does not match the head entry. */
static notrace int kcov_steer_alloc(struct task_struct *t, struct kcov_alloc_ctx *ctx, gfp_t gfp, u32 load_flags)
{
	struct kcov_steer *steer = kcov_steer_find(t);
	unsigned long ip = canonicalize_ip(ctx->addr), flags;
	bool use_chain = ctx->unwind && !(ctx->word0 & KCOV_ALLOC_NOCHAIN);
	struct kcov_steer_entry *e;
	int ret = 0;
	u32 i;

	if (!steer)
		return 0;
@@CONTROL_GFP@@	spin_lock_irqsave(&steer->lock, flags);
	for (i = 0; i < steer->n; i++)
		if (kcov_steer_alloc_names(&steer->e[i], ip, ctx->chain, @@NAMING_CHAIN@@))
			break;
	if (i == steer->n)
		goto out;
	e = steer->head < steer->n ? &steer->e[steer->head] : NULL;
	if (e && kcov_steer_alloc_names(e, ip, ctx->chain, use_chain)) {
		if (!e->draw && (gfp & __GFP_NOFAIL))
			goto out;
		steer->head++;
		ret = !e->draw;
		goto out;
	}
	steer->mismatches++;
	ret = -1;
out:
	spin_unlock_irqrestore(&steer->lock, flags);
	return ret;
}

/* After kcov_alloc_armed was seen set. True: fail the allocation (its record
 * is written here, since the caller returns NULL without the post call).
 * The chain is unwound here, before the allocation, for the steering match
 * and the record. Only armed mode (no KCOV_ALLOC_INVENTORY) is steered. */
bool notrace __kcov_alloc_pre(struct kcov_alloc_ctx *ctx, unsigned long addr, gfp_t gfp, unsigned long size, bool page)
{
	struct task_struct *t = current;
	unsigned int *depth;
	u32 n, flags;
	bool nested;
	int steered;

	if (!kcov_leanux_recording(t))
		return false;
	n = min_t(u32, READ_ONCE(kcov_alloc.n), KCOV_ALLOC_RANGES_MAX);
	flags = READ_ONCE(kcov_alloc.flags);
	if (n ? !kcov_alloc_member(canonicalize_ip(addr), n) : !(flags & KCOV_ALLOC_INVENTORY))
		return false;
	depth = kcov_alloc_depth(t);
	nested = *depth != 0;
	ctx->addr = addr;
	ctx->word0 = (u64)(__force u32)gfp << 32 | min_t(u64, size, KCOV_ALLOC_SIZE_MAX) << 11 |
		     (page ? KCOV_ALLOC_PAGE : 0) | (nested ? KCOV_ALLOC_NESTED : 0);
	ctx->chain[0] = ctx->chain[1] = ctx->chain[2] = ctx->chain[3] = 0;
	/* chains: armed mode always; inventory mode only in pass 2 (ranges)
	 * and not for a refill inside a recorded allocation */
	ctx->unwind = !(flags & KCOV_ALLOC_INVENTORY) || (n && !nested);
	if (ctx->unwind)
		kcov_alloc_chain(addr, &ctx->word0, ctx->chain);
	if (!(flags & KCOV_ALLOC_INVENTORY)) {
		steered = kcov_steer_alloc(t, ctx, gfp, flags);
		if (steered < 0)
			kcov_choice_write(t, 0xffff, addr, NULL, 0);	/* the mismatch marker */
		if (steered > 0) {
			kcov_alloc_record(t, ctx, @@FORCED_OK@@, true);
			return true;
		}
	}
	ctx->active = true;
	(*depth)++;
	return false;
}
EXPORT_SYMBOL(__kcov_alloc_pre);

void notrace __kcov_alloc_post(struct kcov_alloc_ctx *ctx, bool ok)
{
	struct task_struct *t = current;

	ctx->active = false;
	(*kcov_alloc_depth(t))--;
	if (kcov_leanux_recording(t))
		kcov_alloc_record(t, ctx, ok, false);
}
EXPORT_SYMBOL(__kcov_alloc_post);

/*
 * LEANUX A: { u32 n; u32 flags; struct { u64 lo, hi; } ranges[n]; }, the
 * ranges sorted and disjoint, lo < hi, n <= 64, flags 0 or
 * KCOV_ALLOC_INVENTORY. n = 0 and flags = 0 disarms (no records). The set
 * belongs to the instance that loaded it (another instance's load is
 * -EBUSY) and is disarmed with it in kcov_remote_reset.
 */
static long kcov_alloc_load(struct kcov *kcov, void __user *arg)
{
	struct kcov_alloc_range *r = NULL;
	unsigned long irqflags;
	u32 hdr[2], i;
	long ret = 0;

	if (copy_from_user(hdr, arg, sizeof(hdr)))
		return -EFAULT;
	if (hdr[0] > KCOV_ALLOC_RANGES_MAX || (hdr[1] & ~(KCOV_ALLOC_INVENTORY | KCOV_ALLOC_CONTROLS)))
		return -EINVAL;
	if (hdr[0]) {
		r = kmalloc_array(hdr[0], sizeof(*r), GFP_KERNEL);
		if (!r)
			return -ENOMEM;
		if (copy_from_user(r, arg + 8, hdr[0] * sizeof(*r))) {
			kfree(r);
			return -EFAULT;
		}
		for (i = 0; i < hdr[0]; i++)
			if (r[i].lo >= r[i].hi || (i && r[i - 1].hi > r[i].lo)) {
				kfree(r);
				return -EINVAL;
			}
	}
	spin_lock_irqsave(&kcov_remote_lock, irqflags);
	if (kcov_alloc_kcov && kcov_alloc_kcov != kcov) {
		ret = -EBUSY;
	} else {
		WRITE_ONCE(kcov_alloc_armed, 0);
		barrier();
		kcov_alloc.n = hdr[0];
		kcov_alloc.flags = hdr[1];
		for (i = 0; i < hdr[0]; i++)
			kcov_alloc.r[i] = r[i];
		atomic_set(&kcov_alloc_records, 0);
		atomic_set(&kcov_alloc_unwinds, 0);
		atomic64_set(&kcov_alloc_unwind_cycles, 0);
		barrier();
		if (hdr[0] || hdr[1]) {
			kcov_alloc_kcov = kcov;
			WRITE_ONCE(kcov_alloc_armed, 1);
		} else {
			kcov_alloc_kcov = NULL;
		}
	}
	spin_unlock_irqrestore(&kcov_remote_lock, irqflags);
	kfree(r);
	return ret;
}

/* LEANUX A: { u32 records; u32 unwinds; u64 unwind_cycles; } since the
 * load, for the instance that holds the set (-EINVAL otherwise). */
static long kcov_alloc_status(struct kcov *kcov, void __user *arg)
{
	struct { u32 records, unwinds; u64 cycles; } status;
	unsigned long irqflags;

	spin_lock_irqsave(&kcov_remote_lock, irqflags);
	if (kcov_alloc_kcov != kcov) {
		spin_unlock_irqrestore(&kcov_remote_lock, irqflags);
		return -EINVAL;
	}
	status.records = atomic_read(&kcov_alloc_records);
	status.unwinds = atomic_read(&kcov_alloc_unwinds);
	status.cycles = atomic64_read(&kcov_alloc_unwind_cycles);
	spin_unlock_irqrestore(&kcov_remote_lock, irqflags);
	return copy_to_user(arg, &status, sizeof(status)) ? -EFAULT : 0;
}
"""
for k, v in ALLOC_CONTROL_TEXT.items():
    assert s.count(k) == 1, k
    s = s.replace(k, v)
wr('kernel/kcov.c', s)
sub('kernel/kcov.c', '#include <linux/log2.h>\n', '#include <linux/log2.h>\n#include <linux/stacktrace.h>\n#include <linux/timex.h>\n')
sub('kernel/kcov.c', """static struct kcov *kcov_dispatch_kcov;		/* LEANUX: see kcov_dispatch_start */
""", """static struct kcov *kcov_dispatch_kcov;		/* LEANUX: see kcov_dispatch_start */
static struct kcov *kcov_alloc_kcov;		/* LEANUX A: see kcov_alloc_load */
""")
sub('kernel/kcov.c', """	if (kcov_dispatch_kcov == kcov)
		kcov_dispatch_kcov = NULL;	/* LEANUX: disarm with the handles */
""", """	if (kcov_dispatch_kcov == kcov)
		kcov_dispatch_kcov = NULL;	/* LEANUX: disarm with the handles */
	if (kcov_alloc_kcov == kcov) {
		WRITE_ONCE(kcov_alloc_armed, 0);	/* LEANUX A: and the allocation set */
		kcov_alloc_kcov = NULL;
	}
""")
sub('kernel/kcov.c', """	t->kcov_leanux_dropped = 0;
	t->kcov_saved_mode = 0;""", """	t->kcov_leanux_dropped = 0;
	t->kcov_leanux_in_alloc = 0;
	t->kcov_saved_mode = 0;""")
sub('kernel/kcov.c', """#define KCOV_LEANUX_TIME_ADVANCE	_IOW('c', 204, unsigned long)
static long kcov_time_advance(unsigned long __user *arg);
""", """#define KCOV_LEANUX_TIME_ADVANCE	_IOW('c', 204, unsigned long)
static long kcov_time_advance(unsigned long __user *arg);
#define KCOV_LEANUX_ALLOC_LOAD		_IOW('c', 205, unsigned long)
#define KCOV_LEANUX_ALLOC_STATUS	_IOR('c', 206, unsigned long)
static long kcov_alloc_load(struct kcov *kcov, void __user *arg);
static long kcov_alloc_status(struct kcov *kcov, void __user *arg);
#define KCOV_LEANUX_JIFFIES		_IOR('c', 207, unsigned long)
static long kcov_jiffies_read(unsigned long __user *arg);
""")
sub('kernel/kcov.c', """	case KCOV_LEANUX_TIME_ADVANCE:
		return kcov_time_advance((unsigned long __user *)arg);
""", """	case KCOV_LEANUX_TIME_ADVANCE:
		return kcov_time_advance((unsigned long __user *)arg);
	case KCOV_LEANUX_ALLOC_LOAD:
		return kcov_alloc_load(kcov, (void __user *)arg);
	case KCOV_LEANUX_ALLOC_STATUS:
		return kcov_alloc_status(kcov, (void __user *)arg);
	case KCOV_LEANUX_JIFFIES:
		return kcov_jiffies_read((unsigned long __user *)arg);
""")
sub('kernel/kcov.c', """	u32 draw;
	u32 pad;
	u8 value[40];
};""", """	u32 draw;
	u32 flags;		/* LEANUX A: KCOV_STEER_CHAIN (kind 305 only) */
	u8 value[40];
};
#define KCOV_STEER_CHAIN 1	/* LEANUX A: match the unwound chain too (section 5.2) */""")
sub('kernel/kcov.c', """		for (j = 0; j < KCOV_STEER_IPS; j++)
			if (steer->e[i].ips[j] == ip)
				return true;
	return false;""", """		for (j = 0; j < KCOV_STEER_IPS; j++)
			if (steer->e[i].kind != 305 && steer->e[i].ips[j] == ip)
				return true;	/* LEANUX A: kind 305 names by chain */
	return false;""")
sub('kernel/kcov.c', """	for (i = 0; i < n; i++)
		if (steer->e[i].len > sizeof(steer->e[i].value)) {""", """	for (i = 0; i < n; i++)
		if (steer->e[i].len > sizeof(steer->e[i].value) ||
		    /* LEANUX A: kind 305 entries are draw or fail (8 zero bytes) */
		    (steer->e[i].kind == 305 ? steer->e[i].len != 8 || (steer->e[i].flags & ~KCOV_STEER_CHAIN) ||
		     (!steer->e[i].draw && memchr_inv(steer->e[i].value, 0, 8)) : steer->e[i].flags)) {""")
sub('include/linux/sched.h', """	/* LEANUX: whether the task is in a dispatch section: */
	unsigned int			kcov_leanux_section;
""", """	/* LEANUX: whether the task is in a dispatch section: */
	unsigned int			kcov_leanux_section;

	/* LEANUX A: recorded allocations in progress in task context: */
	unsigned int			kcov_leanux_in_alloc;
""")
ALLOC_H = '''/*
 * LEANUX A (docs/2026-10-05-a-alloc.md, section 4): the allocation hook, in
 * slab_alloc_node and __alloc_pages_noprof. Unarmed, one load. pre returns
 * true to fail the allocation (a steered failure, stream K2).
 */
struct kcov_alloc_ctx { unsigned long addr; u64 word0; u64 chain[4]; bool active, unwind; };
extern u32 kcov_alloc_armed;
bool __kcov_alloc_pre(struct kcov_alloc_ctx *ctx, unsigned long addr, gfp_t gfp, unsigned long size, bool page);
void __kcov_alloc_post(struct kcov_alloc_ctx *ctx, bool ok);
static __always_inline bool kcov_alloc_pre(struct kcov_alloc_ctx *ctx, unsigned long addr, gfp_t gfp,
					   unsigned long size, bool page)
{
	ctx->active = false;
	if (likely(!READ_ONCE(kcov_alloc_armed)))
		return false;
	return __kcov_alloc_pre(ctx, addr, gfp, size, page);
}
static __always_inline void kcov_alloc_post(struct kcov_alloc_ctx *ctx, bool ok)
{
	if (unlikely(ctx->active))
		__kcov_alloc_post(ctx, ok);
}
'''
sub('include/linux/kcov.h', """/* LEANUX D3: mod_timer's arm record (kind 303). */
void kcov_timer_arm(void *func, unsigned long now, unsigned long expires, unsigned long ip, void *timer);
""", """/* LEANUX D3: mod_timer's arm record (kind 303). */
void kcov_timer_arm(void *func, unsigned long now, unsigned long expires, unsigned long ip, void *timer);
""" + ALLOC_H)
sub('include/linux/kcov.h', """static inline void kcov_timer_arm(void *func, unsigned long now, unsigned long expires, unsigned long ip, void *timer) {}
""", """static inline void kcov_timer_arm(void *func, unsigned long now, unsigned long expires, unsigned long ip, void *timer) {}
struct kcov_alloc_ctx { };
static inline bool kcov_alloc_pre(struct kcov_alloc_ctx *ctx, unsigned long addr, gfp_t gfp,
				  unsigned long size, bool page) { return false; }
static inline void kcov_alloc_post(struct kcov_alloc_ctx *ctx, bool ok) {}
""")
SL = 'mm/slub.c'
sub(SL, '#include <linux/sort.h>\n', '#include <linux/sort.h>\n#include <linux/kcov.h>\n')
sub(SL, """	void *object;
	bool init = false;

	s = slab_pre_alloc_hook(s, gfpflags);
	if (unlikely(!s))
		return NULL;
""", """	void *object;
	bool init = false;
	struct kcov_alloc_ctx kctx;	/* LEANUX A */

	/* LEANUX A: the allocation hook; a forced failure is recorded by pre */
	if (kcov_alloc_pre(&kctx, addr, gfpflags & gfp_allowed_mask, orig_size, false))
		return NULL;
	s = slab_pre_alloc_hook(s, gfpflags);
	if (unlikely(!s)) {
		kcov_alloc_post(&kctx, false);
		return NULL;
	}
""")
sub(SL, """	slab_post_alloc_hook(s, lru, gfpflags, 1, &object, init, orig_size);

	return object;
}
""", """	slab_post_alloc_hook(s, lru, gfpflags, 1, &object, init, orig_size);
	kcov_alloc_post(&kctx, object != NULL);	/* LEANUX A */

	return object;
}
""")
PA = 'mm/page_alloc.c'
sub(PA, '#include <linux/pgalloc_tag.h>\n', '#include <linux/pgalloc_tag.h>\n#include <linux/kcov.h>\n')
sub(PA, """	gfp_t alloc_gfp; /* The gfp_t that was actually used for allocation */
	struct alloc_context ac = { };
""", """	gfp_t alloc_gfp; /* The gfp_t that was actually used for allocation */
	struct alloc_context ac = { };
	struct kcov_alloc_ctx kctx;	/* LEANUX A */
""")
sub(PA, """	gfp = current_gfp_context(gfp);
	alloc_gfp = gfp;
	if (!prepare_alloc_pages(gfp, order, preferred_nid, nodemask, &ac,
			&alloc_gfp, &alloc_flags))
		return NULL;
""", """	gfp = current_gfp_context(gfp);
	alloc_gfp = gfp;
	/* LEANUX A: the allocation hook; a forced failure is recorded by pre */
	if (kcov_alloc_pre(&kctx, _RET_IP_, gfp, order, true))
		return NULL;
	if (!prepare_alloc_pages(gfp, order, preferred_nid, nodemask, &ac,
			&alloc_gfp, &alloc_flags)) {
		kcov_alloc_post(&kctx, false);
		return NULL;
	}
""")
sub(PA, """	kmsan_alloc_page(page, order, alloc_gfp);

	return page;
}""", """	kmsan_alloc_page(page, order, alloc_gfp);
	kcov_alloc_post(&kctx, page != NULL);	/* LEANUX A */

	return page;
}""")
# ---- D3+A integration: the dispatch set's capacity (record-only infrastructure) ----
# KCOV_DISPATCH_MAX 16 -> 32: room for more dispatch functions in the load
# (harness/guest.c DISPATCH_MAX, harness/trace.py serialize_wire match it).
# The load still refuses n = 0 and n > KCOV_DISPATCH_MAX; nothing else changes.
sub('kernel/kcov.c', "#define KCOV_DISPATCH_MAX 16\n/* LEANUX D3", "#define KCOV_DISPATCH_MAX 32\n/* LEANUX D3")
files=TOUCHED
out=[]
for f in files:
    r=subprocess.run(['diff','-u','--label','a/'+f,'--label','b/'+f,f'{WD}/base/{f}',f'{N}/{f}'],capture_output=True,text=True)
    assert r.returncode==1,(f,r.stderr); out.append(r.stdout)
open('kernel/patches/choice-stream-alloc-controls.patch' if CONTROLS else 'kernel/patches/choice-stream.patch','w').write(''.join(out))
print('ok')
