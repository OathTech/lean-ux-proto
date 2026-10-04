#!/usr/bin/env python3
"""Generate kernel/patches/choice-stream.patch from the locked source.

Run from the repository root: copies the touched files from .deps/linux into
.artifacts/choice-patch/{base,new}, edits `new`, and writes the unified diff.
The patch applies to the pristine tree (scripts/apply-kernel-patch.py); it
touches no file the check anchors (correspondence/kcov.json "files").
Edits: kcov_choice_ip and steering (choice-stream strategy, steps 1-2); the
random and clock hooks; dispatch sections in process_one_work and the NET_RX
vector (D1 sprint, stream A).
"""
import sys, re, os, shutil, subprocess
WD='.artifacts/choice-patch'; N=WD+'/new'
SOURCE=os.environ.get('LEANUX_SHARED_ROOT', '.') + '/.deps/linux'
TOUCHED=['kernel/kcov.c','include/linux/kcov.h','include/linux/sched.h','drivers/char/random.c',
         'kernel/time/timekeeping.c','kernel/workqueue.c','kernel/softirq.c']
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
 * process. The schedule covers every encounter of the call sites it names,
 * in order: each entry gives the site's return addresses and kind, and
 * either a value to substitute or "draw" (keep the kernel's value). A hook
 * at a named site that does not match the head entry is a mismatch: a marker
 * record is written and the entry stays. Other sites are not steered. The
 * parent reads the remaining entries and mismatches back
 * (KCOV_LEANUX_STEER_STATUS). Only recording contexts consult the schedule.
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

static void notrace kcov_choice_write(struct task_struct *t, u32 kind, unsigned long ip, const void *data, unsigned int len)
{
	const u8 *bytes = data;
	u64 words[KCOV_CHOICE_MAX_WORDS + 1] = {0};
	unsigned int n = len > 8 * KCOV_CHOICE_MAX_WORDS ? 8 * KCOV_CHOICE_MAX_WORDS : len;
	unsigned int nwords = DIV_ROUND_UP(n, 8), i;
	u64 *area, seq;

	if (check_kcov_mode(KCOV_MODE_TRACE_PC, t)) {
		u64 pos;

		for (i = 0; i < n; i++)
			words[i / 8] |= (u64)bytes[i] << (8 * (i % 8));
		area = (u64 *)t->kcov_area;
		pos = READ_ONCE(area[0]);
		if (pos + 3 + nwords >= t->kcov_size) {
			WRITE_ONCE(area[0], t->kcov_size - 1);
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
		   check_kcov_mode(KCOV_MODE_TRACE_CMP, t)) {
		u64 count, start, nrec = 1 + DIV_ROUND_UP(nwords, 3), r;

		for (i = 0; i < n; i++)
			words[i / 8] |= (u64)bytes[i] << (8 * (i % 8));
		area = (u64 *)t->kcov_area;
		count = READ_ONCE(area[0]);
		start = 1 + count * KCOV_WORDS_PER_CMP;
		if ((start + nrec * KCOV_WORDS_PER_CMP) * sizeof(u64) >
		    t->kcov_size * sizeof(unsigned long)) {
			WRITE_ONCE(area[0], (t->kcov_size - 1) / KCOV_WORDS_PER_CMP);
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
 * section writes a start record (kind 300, the function's address) and a
 * stop record (kind 301, the number of records dropped in the section),
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

void notrace kcov_dispatch_start(struct kcov_dispatch_section *s, void *func)
{
	struct task_struct *t = current;
	struct kcov *kcov;
	unsigned long flags, ip = (unsigned long)func;
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
	kcov_choice_write(t, 300, _RET_IP_, &ip, sizeof(ip));
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
}
EXPORT_SYMBOL(kcov_dispatch_stop);

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
sub('kernel/kcov.c', """		if (pos + 3 + nwords >= t->kcov_size) {
			WRITE_ONCE(area[0], t->kcov_size - 1);
			return;
		}""", """		if (pos + 3 + nwords >= t->kcov_size) {
			WRITE_ONCE(area[0], t->kcov_size - 1);
			t->kcov_leanux_dropped++;
			return;
		}""")
sub('kernel/kcov.c', """		    t->kcov_size * sizeof(unsigned long)) {
			WRITE_ONCE(area[0], (t->kcov_size - 1) / KCOV_WORDS_PER_CMP);
			return;
		}""", """		    t->kcov_size * sizeof(unsigned long)) {
			WRITE_ONCE(area[0], (t->kcov_size - 1) / KCOV_WORDS_PER_CMP);
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
    'void kcov_dispatch_start(struct kcov_dispatch_section *s, void *func);\n'
    'void kcov_dispatch_stop(struct kcov_dispatch_section *s);\n')
sub('include/linux/kcov.h', 'static inline void kcov_choice_ip(u32 kind, unsigned long ip, void *data, unsigned int len) {}\n',
    'static inline void kcov_choice_ip(u32 kind, unsigned long ip, void *data, unsigned int len) {}\n'
    'struct kcov_dispatch_section { bool open; };\n'
    'static inline void kcov_dispatch_start(struct kcov_dispatch_section *s, void *func) {}\n'
    'static inline void kcov_dispatch_stop(struct kcov_dispatch_section *s) {}\n')
sub('include/linux/sched.h', """	/* Collect coverage from softirq context: */
	unsigned int			kcov_softirq;
""", """	/* Collect coverage from softirq context: */
	unsigned int			kcov_softirq;

	/* LEANUX: records dropped in the current dispatch section: */
	unsigned int			kcov_leanux_dropped;
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
	kcov_dispatch_start(&section, worker->current_func);	/* LEANUX */
	worker->current_func(work);
	kcov_dispatch_stop(&section);
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
			kcov_dispatch_start(&section, h->action);
		h->action();
		kcov_dispatch_stop(&section);
""")
files=TOUCHED
out=[]
for f in files:
    r=subprocess.run(['diff','-u','--label','a/'+f,'--label','b/'+f,f'{WD}/base/{f}',f'{N}/{f}'],capture_output=True,text=True)
    assert r.returncode==1,(f,r.stderr); out.append(r.stdout)
open('kernel/patches/choice-stream.patch','w').write(''.join(out))
print('ok')
