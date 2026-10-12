/* Linux observations only. Run inside the pinned QEMU guest, never on the host. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <limits.h>
#include <linux/genetlink.h>
#include <linux/if_link.h>
#include <linux/kcov.h>
#include <linux/netlink.h>
#include <linux/rtnetlink.h>
#include <linux/wireguard.h>
#include <linux/io_uring.h>
#include <net/if.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <time.h>
#include <sched.h>
#include <signal.h>
#include <sys/socket.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/syscall.h>
#include <sys/utsname.h>
#include <sys/wait.h>
#include <unistd.h>
#include <netinet/udp.h>
#ifndef UDP_SEGMENT
#define UDP_SEGMENT 103   /* W4: linux/udp.h */
#endif
#ifndef SOL_UDP
#define SOL_UDP 17
#endif

#define MAX_OPS 64
/* The KCOV area in words, task and remote alike (L, docs/2026-10-05-l-lifecycle.md
 * section 10: a wg_create window's comparison child exceeds 64 K words; E-B: an
 * io_uring flood crossing 512 runs ~600 UDP sends inline in the trace task with
 * KCOV on, so both streams need headroom). The host's bounds follow it
 * (harness/trace.py KCOV_CAPACITY). */
#define CAPACITY (4096UL * 1024)
/* W7 (design section 12): a wg_batch of 1025 keepalive-size items is about
 * 55 KB on the wire; the per-operation payload and the line buffer hold it. */
#define MAX_PAYLOAD 65536
#define NETLINK_FD 7
/* Stage B1 network fixture: UDP listeners that catch what wg0 sends to
 * 127.0.0.1 / ::1 at LISTEN_PORT, and a dual-stack UDP socket whose datagrams
 * the routes added at wg_up send into wg0. */
#define LISTEN4_FD 4
#define LISTEN6_FD 5
#define SEND_FD 6
#define SEND_PORT 40000
/* The sender is bound to this port, so a peer endpoint learned from its
 * datagrams (a consumed handshake initiation) is deterministic. */
#define SENDER_PORT 51998
#define LISTEN_PORT 51999
/* wg_observe waits this long for the handshake workers before it looks. */
#define OBSERVE_WAIT_US 400000
#define QUEUE_WAIT_US 100000
/* W8 (docs/2026-10-06-w8-w9-netns-routing.md, sections 3.1-3.2): the
 * foreign-creator fixture ("net_fixture": "foreign-creator", net 3). wg0
 * lives in the device namespace D with the trace process, the inner sender
 * (6) and the generic-netlink socket (7); its outer side lives in the
 * creating namespace C: the listeners (4, 5), the injector (8, the outer
 * sender at SENDER_PORT) and the pin (9, an open /proc/self/ns/net).
 * wg_netns_close closes the injector and the listeners, whose put_net is
 * RCU-deferred, lets those run (NETNS_SETTLE_US), then closes the pin: the
 * last reference, so cleanup_net is queued inside that close (its kind-307
 * record in this operation's task stream), and waits NETNS_WAIT_US for the
 * teardown's section. The parked namespace descriptors and the pin
 * handshake with the holder sit above the descriptors the fixture checks
 * (3-31) but below NR_OPEN_DEFAULT (64), so the descriptor table never
 * grows (its size is an operand of every close); all are closed before
 * the first window. The settle between the closes is a TSC spin, not a
 * sleep: a nanosleep inside the window would record its clock reads. */
#define INJECT_FD 8
#define PIN_FD 9
#define NETNS_SETTLE_US 100000
#define NETNS_WAIT_US 1000000
#define PARK_D_FD 40
#define PARK_C_FD 41
#define PIN_SIGNAL_FD 42
#define PIN_ACK_FD 43
/* A wg_xmit payload: at most wg0's MTU (1420) less the IPv4 and UDP headers,
 * or (W4) two full-size UDP_SEGMENT segments. */
#define MAX_XMIT_PAYLOAD 2784
/* W4: the fixture's routes into wg0 with an MTU ("net_fixture": {"routes"}). */
#define MAX_FIXTURE_ROUTES 8
struct fixture_route { unsigned family; unsigned char dst[16]; unsigned mtu; };
/* No WireGuard timer is armed before wg_up (mod_peer_timer needs a running
 * device). Counted from just before the wg_up ioctl, in real time (the
 * virtual advances of wg_advance are subtracted), a trace must end within
 * 4.5 s: REKEY_TIMEOUT (5 s) less a 0.5 s margin; the mirror's firing window
 * (Leanux/Env.lean TRACE_BOUND_MS, Timing.traceBound) uses the same bound.
 * 4.5 s, not 4 s: on a contended host b2_lengths (3.3 s of waits) took
 * 3.80 s (2026-10-06, docs/2026-10-06-contended-host.md). */
#define REKEY_BOUND_NS 4500000000LL
/* D3 (docs/2026-10-05-d3-timers.md, section 4.3): wg_advance moves jiffies by
 * `ticks` (KCOV_LEANUX_TIME_ADVANCE on the trace's own KCOV descriptor); the
 * timekeeper (refined-jiffies) follows at the next tick, which also runs the
 * due timers. The guest first waits for that tick (the monotonic clock has
 * absorbed the jump: a sleep begun before it would end at that same tick),
 * then ADVANCE_WAIT_US for the callbacks' work and loopback delivery. */
#define KCOV_LEANUX_TIME_ADVANCE _IOW('c', 204, unsigned long)
/* The wait-0 control (docs/2026-10-05-d3-timers.md, section 8) builds the
 * guest with -DADVANCE_WAIT_US=0 -DADVANCE_ABSORB=0 (harness/linux.py,
 * GUEST_VARIANTS): wg_advance returns at once, so the callbacks' sections and
 * the work they queue land in the next operation. */
#ifndef ADVANCE_WAIT_US
#define ADVANCE_WAIT_US 100000
#endif
#ifndef ADVANCE_ABSORB
#define ADVANCE_ABSORB 1
#endif
#define TICK_NS 4000000LL           /* CONFIG_HZ=250 */
#define EXPECTED_CLOCKSOURCE "refined-jiffies"
/* Pipes (docs/2026-10-05-p-pipes.md section 6): read and write byte counts
 * up to MAX_IO (17 pages); a read is observed as its first READ_HEAD bytes and
 * a BLAKE2s-256 digest of all of them; pause_ms (at most PAUSE_MS_MAX) is
 * slept before an operation's coverage reset. */
#define MAX_IO 69632
#define READ_HEAD 64
#define PAUSE_MS_MAX 20
/* Wire opcodes: the explicit table of harness/trace.py OPCODES (unit test
 * harness/test_trace.py OpcodeTableTests checks that the two agree). 15-18
 * are reserved there (L: wg_create, wg_down, wg_delete; E: wg_flood) and
 * fall to the default case here until implemented. */
#define OP_EVENTFD2 1
#define OP_DUP 2
#define OP_DUP3 3
#define OP_CLOSE 4
#define OP_READ 5
#define OP_WRITE 6
#define OP_FCNTL 7
#define OP_WG_SET 8
#define OP_WG_GET 9
#define OP_WG_UP 10
#define OP_WG_XMIT 11
#define OP_WG_OBSERVE 12
#define OP_WG_INJECT 13
#define OP_PIPE2 14
#define OP_WG_CREATE 15
#define OP_WG_DOWN 16
#define OP_WG_DELETE 17
#define OP_WG_FLOOD 18
#define OP_WG_ADVANCE 19
#define OP_WG_NETNS_CLOSE 22
#define OP_WG_DELADDR 23
#define OP_WG_DELROUTE 24
/* W4 (docs/2026-10-06-w4-w7-transmit-bulk.md section 6): SIOCSIFMTU on wg0; W7: the batch. */
#define OP_WG_SET_MTU 25
#define OP_WG_BATCH 26
/* 20-21 are reserved for W2 (harness/trace.py RESERVED_OPCODES,
 * docs/2026-10-11-interface.md): wg_get_start and wg_get_recv. No define
 * until the stream lands: the opcode switch's default fails any such code.
 * W8 took 22 (wg_netns_close), W9 23-24, W4 25, W7 26. */
#define IS_LIFECYCLE_OP(code) ((code) == OP_WG_CREATE || (code) == OP_WG_DOWN || (code) == OP_WG_DELETE)
/* The parent's per-child hang guard (P design section 6): a child still
 * running after this many seconds is killed with its process group. */
#define WATCHDOG_BASE_SECONDS 60
#define WATCHDOG_OP_SECONDS 3
struct operation { unsigned code, kind, newkind, a, b, pause_ms; long long fd, newfd; uint64_t value;
                   unsigned char payload[MAX_PAYLOAD]; size_t payload_len; };
/* A steering schedule entry (the patched kernel's struct kcov_steer_entry;
 * docs/2026-10-03-choice-stream-strategy.md, step 2). */
#define STEER_MAX 64
struct steer_entry { uint64_t ips[4]; uint32_t kind, len, draw, flags; unsigned char value[40]; };
/* flags: match the unwound chain too (kind 305 only; A, section 5.2) */
#define STEER_CHAIN 1
struct steer_arg { uint32_t n, pad; struct steer_entry e[STEER_MAX]; };
#define KCOV_LEANUX_STEER_LOAD _IOW('c', 200, unsigned long)
#define KCOV_LEANUX_STEER_STATUS _IOR('c', 201, unsigned long)
/* The dispatch set (choice-stream strategy, section 4.4): the addresses of
 * the deferred units whose dispatch opens a KCOV section, resolved by the
 * host; one per batch. */
#define DISPATCH_MAX 32   /* the kernel's KCOV_DISPATCH_MAX */
struct dispatch_arg { uint32_t n, flags; uint64_t funcs[DISPATCH_MAX]; };
/* W8: the subset of the batch's dispatch set this trace arms (its `arm`
 * bits), loaded on the remote instance; the kernel opens sections and
 * writes queue records for these functions only. */
static struct dispatch_arg trace_dispatch;
/* W8: the pin holder, a process forked once by the batch, keeps an open
 * /proc/<pid>/ns/net of every foreign-creator trace process's D until the
 * batch ends (section 3.2, C1: D's teardown never runs while a later run is
 * armed with cleanup_net). The pins live in the holder, not the batch, so no
 * child inherits one (an inherited descriptor would shift the fixture and
 * widen the descriptor table). Two AF_UNIX socket pairs, made once and
 * inherited by every child: signal (a trace process writes its pid on [1],
 * the holder reads [0]) and ack (the holder answers 'k' on [3], or 'n' if
 * the open failed; the trace reads [2]); every child moves its ends above
 * the descriptors a trace can see and closes the originals. Socket pairs,
 * not pipes: a pipe's buffers are charged to the user's pipe_bufs, the
 * operand every pipe trace's alloc_pipe_info compares
 * (too_many_pipe_buffers_soft), so two batch pipes shifted every pipe
 * trace's operands by 32. */
static int pin_sock[4] = {-1, -1, -1, -1};
static int netns_closed;

static void pin_holder(void)
{
    struct rlimit pins = {2 * 4096 + 64, 2 * 4096 + 64};
    if (setrlimit(RLIMIT_NOFILE, &pins)) _exit(3);
    if (close(pin_sock[1]) || close(pin_sock[2])) _exit(3);
    for (;;) {
        pid_t pid;
        ssize_t n = read(pin_sock[0], &pid, sizeof(pid));
        if (n == 0) _exit(0);   /* the batch is gone: the pins go with this process */
        if (n != (ssize_t)sizeof(pid)) _exit(3);
        char path[64];
        snprintf(path, sizeof(path), "/proc/%d/ns/net", (int)pid);
        int pin = open(path, O_RDONLY);
        if (write(pin_sock[3], pin < 0 ? "n" : "k", 1) != 1) _exit(3);
    }
}
/* flags: write the kind-303 arm records (D3), from the wire's A line */
#define DISPATCH_ARM_RECORDS 1
static struct dispatch_arg dispatch;
#define KCOV_LEANUX_DISPATCH_LOAD _IOW('c', 202, unsigned long)
#define KCOV_LEANUX_SECTION_STATUS _IOR('c', 203, unsigned long)
/* The allocation set (A, docs/2026-10-05-a-alloc.md section 4.3), one per
 * batch from the wire's M line: n sorted [lo, hi) ranges and flags (1: the
 * inventory mode). n = 0 and flags = 0 is disarmed: no load, no records. The
 * trace process loads it on its own KCOV descriptor before it enables
 * coverage; the kernel disarms it when that descriptor's instance goes. */
#define ALLOC_RANGES_MAX 64
#define ALLOC_INVENTORY 1
struct alloc_arg { uint32_t n, flags; struct { uint64_t lo, hi; } r[ALLOC_RANGES_MAX]; };
static struct alloc_arg alloc;
#define KCOV_LEANUX_ALLOC_LOAD _IOW('c', 205, unsigned long)
#define KCOV_LEANUX_ALLOC_STATUS _IOR('c', 206, unsigned long)
struct trace {
    /* net: 0 no network fixture, 1 the fixture with a down wg0, 2 the bare
     * network fixture without wg0 (L, "net_fixture": "bare"), 3 the
     * foreign-creator fixture (W8); arm: the trace's subset of the batch's
     * dispatch set, a bit per entry (W8: per-trace arming, section 3.2) */
    char id[81]; unsigned count; unsigned rlimit; unsigned net; unsigned arm; struct operation ops[MAX_OPS];
    unsigned nsteer; struct steer_entry steer[STEER_MAX];
    unsigned nroutes; struct fixture_route routes[MAX_FIXTURE_ROUTES];
};
/* W4: the running trace's fixture routes, for route_into_wg0. */
static const struct fixture_route *fixture_routes;
static unsigned n_fixture_routes;
static char line[4 * MAX_PAYLOAD];
/* fds: a successful pipe2's pair; digest: BLAKE2s-256 of all bytes a read
 * returned; sigpipe: SIGPIPE pending after a write. */
struct observation { long ret; int error; unsigned char bytes[READ_HEAD]; unsigned char digest[32];
                     int fds[2]; int sigpipe; };
/* The caller's buffers for read and write, page-aligned; every page is
 * written once in each trace child before KCOV_ENABLE, so no page fault lands
 * in a coverage window. */
static unsigned char read_buffer[MAX_IO] __attribute__((aligned(4096)));
static unsigned char write_buffer[MAX_IO] __attribute__((aligned(4096)));

/* Set in a trace process once its network namespace exists: fail() then
 * deletes wg0 before exiting (L, docs/2026-10-05-l-lifecycle.md section 2.4,
 * audit M1), so wg_destruct runs synchronously in this task rather than in
 * an asynchronous netns cleanup that could fall into the next trace. */
static int net_live;
static void delete_wg0_best_effort(void);

static void fail(const char *id, int index, const char *kind, const char *detail)
{
    printf("LEANUX_ERROR {\"id\":\"%s\",\"index\":%d,\"kind\":\"%s\",\"detail\":\"%s\",\"errno\":%d}\n",
           id, index, kind, detail, errno);
    fflush(stdout);
    /* At most once: the teardown itself never calls fail(). */
    if (net_live) {
        net_live = 0;
        delete_wg0_best_effort();
    }
    _exit(1);
}

/* ---- BLAKE2s-256 (RFC 7693), unkeyed -------------------------------------
 * The digest of a read's bytes (P design section 6, Q1). The mirror computes
 * it with Leanux/WG/Blake2s.lean and the host recomputes it with hashlib for
 * reads of at most READ_HEAD bytes; this implementation is self-tested at
 * startup (blake2s_self_test) and the batch fails if it disagrees. */
static const uint32_t blake2s_iv[8] = {0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
                                       0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19};
static const unsigned char blake2s_sigma[10][16] = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}, {14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3},
    {11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4}, {7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8},
    {9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13}, {2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9},
    {12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11}, {13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10},
    {6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5}, {10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0}};

static uint32_t rotr32(uint32_t x, unsigned n) { return (x >> n) | (x << (32 - n)); }

#define BLAKE2S_G(a, b, c, d, x, y) do { \
    v[a] += v[b] + (x); v[d] = rotr32(v[d] ^ v[a], 16); v[c] += v[d]; v[b] = rotr32(v[b] ^ v[c], 12); \
    v[a] += v[b] + (y); v[d] = rotr32(v[d] ^ v[a], 8); v[c] += v[d]; v[b] = rotr32(v[b] ^ v[c], 7); } while (0)

static void blake2s_compress(uint32_t h[8], const unsigned char block[64], uint64_t t, int last)
{
    uint32_t m[16], v[16];
    for (int i = 0; i < 16; ++i)
        m[i] = (uint32_t)block[4 * i] | (uint32_t)block[4 * i + 1] << 8 | (uint32_t)block[4 * i + 2] << 16 |
               (uint32_t)block[4 * i + 3] << 24;
    for (int i = 0; i < 8; ++i) { v[i] = h[i]; v[i + 8] = blake2s_iv[i]; }
    v[12] ^= (uint32_t)t;
    v[13] ^= (uint32_t)(t >> 32);
    if (last) v[14] = ~v[14];
    for (int r = 0; r < 10; ++r) {
        const unsigned char *s = blake2s_sigma[r];
        BLAKE2S_G(0, 4, 8, 12, m[s[0]], m[s[1]]);
        BLAKE2S_G(1, 5, 9, 13, m[s[2]], m[s[3]]);
        BLAKE2S_G(2, 6, 10, 14, m[s[4]], m[s[5]]);
        BLAKE2S_G(3, 7, 11, 15, m[s[6]], m[s[7]]);
        BLAKE2S_G(0, 5, 10, 15, m[s[8]], m[s[9]]);
        BLAKE2S_G(1, 6, 11, 12, m[s[10]], m[s[11]]);
        BLAKE2S_G(2, 7, 8, 13, m[s[12]], m[s[13]]);
        BLAKE2S_G(3, 4, 9, 14, m[s[14]], m[s[15]]);
    }
    for (int i = 0; i < 8; ++i) h[i] ^= v[i] ^ v[i + 8];
}

static void blake2s256(const unsigned char *data, size_t len, unsigned char out[32])
{
    uint32_t h[8];
    unsigned char block[64];
    memcpy(h, blake2s_iv, sizeof(h));
    h[0] ^= 0x01010000 | 32;   /* depth 1, fanout 1, no key, 32-byte digest */
    size_t done = 0;
    /* every block but the last is full and not final; the last (possibly
     * empty, zero-padded) block carries the total length and the final flag */
    while (len - done > 64) {
        blake2s_compress(h, data + done, done + 64, 0);
        done += 64;
    }
    memset(block, 0, sizeof(block));
    if (len) memcpy(block, data + done, len - done);
    blake2s_compress(h, block, len, 1);
    for (int i = 0; i < 32; ++i) out[i] = (unsigned char)(h[i / 4] >> (8 * (i % 4)));
}

/* Vectors from Python's hashlib.blake2s (the first three are also the
 * mirror's, Leanux/WG/Blake2s.lean): empty, one partial block, exactly one
 * block, one byte past it, a multi-block input, and MAX_IO bytes. */
static void blake2s_self_test(void)
{
    static const struct { size_t len; int kind; const char *hex; } vectors[] = {
        {0, 0, "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9"},
        {3, 1, "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982"},   /* "abc" */
        {64, 0, "56f34e8b96557e90c1f24b52d0c89d51086acf1b00f634cf1dde9233b8eaaa3e"},  /* bytes 0..63 */
        {65, 0, "1b53ee94aaf34e4b159d48de352c7f0661d0a40edff95a0b1639b4090e974472"},
        {200, 0, "6d244e1a06ce4ef578dd0f63aff0936706735119ca9c8d22d86c801414ab9741"},
        {MAX_IO, 2, "7537c8397db7a1f5ace6b25c1e81d858303da18987a96c06b571f4e5b66121a7"}, /* k mod 251 */
    };
    for (size_t v = 0; v < sizeof(vectors) / sizeof(vectors[0]); ++v) {
        for (size_t k = 0; k < vectors[v].len; ++k)
            read_buffer[k] = vectors[v].kind == 1 ? (unsigned char)"abc"[k]
                           : (unsigned char)(vectors[v].kind == 2 ? k % 251 : k);
        unsigned char digest[32];
        char hex[65];
        blake2s256(read_buffer, vectors[v].len, digest);
        for (int i = 0; i < 32; ++i) sprintf(hex + 2 * i, "%02x", digest[i]);
        if (strcmp(hex, vectors[v].hex)) fail("batch", -1, "environment_failure", "blake2s_self_test");
    }
}

/* W7 stream H (docs/2026-10-06-w4-w7-transmit-bulk.md, 13.2 (ii)): the
 * dispatch-section block (1-based, in area order) each kept comparison
 * record of the remote area lies in, 0 outside any: split_hidden fills it
 * while compacting, print_records prints it as a fifth element and keeps
 * equal records of different blocks apart. */
static unsigned short cmp_block[CAPACITY / 4];

/* Deduplication of an area before printing (W7, probe P-A, section 12 of
 * docs/2026-10-06-w4-w7-transmit-bulk.md): an open-addressing table over
 * area positions, one pass in area order, in place of the sort over every
 * occurrence it replaced. At a 1024-item batch that sort cost the PC child
 * 2.3 s and the comparison child 7 s of the 4.5 s rekey bound, against
 * 0.12 s for the kernel's own work. A slot holds a distinct entry's index
 * (1-based) under the pass that wrote it: a slot of an earlier pass reads
 * as empty, so a pass clears nothing (a 16 MiB memset per pass would cost
 * every trace tens of milliseconds under TCG). More distinct entries than
 * half the slots fails the trace rather than degrading. */
#define DEDUP_SLOTS (2UL * 1024 * 1024)
#define DEDUP_MASK (DEDUP_SLOTS - 1)
struct dedup_slot { unsigned pass, value; };
static struct dedup_slot dedup_table[DEDUP_SLOTS];
static unsigned dedup_pass;

static void dedup_begin(void)
{
    if (!++dedup_pass) {   /* the pass counter wrapped: clear once */
        memset(dedup_table, 0, sizeof dedup_table);
        dedup_pass = 1;
    }
}

static unsigned dedup_at(unsigned long h)
{
    return dedup_table[h].pass == dedup_pass ? dedup_table[h].value : 0;
}

static void dedup_set(unsigned long h, unsigned value)
{
    dedup_table[h] = (struct dedup_slot){ .pass = dedup_pass, .value = value };
}
/* a distinct comparison record: the area position of its first occurrence
 * and, in the remote area, its blocks as a chain of ranges (area order) and
 * whether it occurred outside any block */
struct distinct_record { unsigned position, head, tail, zero; };
static struct distinct_record distinct[CAPACITY / 4];
struct block_range { unsigned short lo, hi; unsigned next; };
static struct block_range ranges[CAPACITY / 4];
static const unsigned long *sort_area;   /* the area compare_distinct reads */
/* a bulk trace's rows, written after its last operation (execute) */
static char bulk_out[16UL * 1024 * 1024];

static unsigned long hash_words(const unsigned long *words, unsigned n)
{
    unsigned long h = 0x9E3779B97F4A7C15UL;
    for (unsigned k = 0; k < n; ++k) {
        h ^= words[k];
        h *= 0xBF58476D1CE4E5B9UL;
        h ^= h >> 29;
    }
    return h;
}

static int compare_distinct(const void *a, const void *b)
{
    const struct distinct_record *x = a, *y = b;
    return memcmp(sort_area + 1 + 4 * (unsigned long)x->position, sort_area + 1 + 4 * (unsigned long)y->position,
                  4 * sizeof(unsigned long));
}

/* ---- Netlink (network fixture traces only) ---------------------------- */
/* W2 (docs/2026-10-06-w1-w2-netlink.md, 4.1): every netlink receive uses a
 * buffer of exactly NLMSG_GOODSIZE = SKB_WITH_OVERHEAD(PAGE_SIZE) = 3776 bytes
 * (sizeof(struct skb_shared_info) 320, the reference vmlinux's DWARF). The
 * socket's max_recvmsg_len then never exceeds it, so every dump skb is
 * alloc_skb(NLMSG_GOODSIZE, GFP_KERNEL) with exactly 3776 bytes of room
 * (af_netlink.c:2279-2312): the chunk budget the mirror computes. */
#define NL_RECV_LEN 3776
static unsigned char nl_buffer[NL_RECV_LEN];
static unsigned short wg_family;

/* One receive of at most NL_RECV_LEN bytes (W2 4.1). A longer message is
 * truncated by the kernel and the rest discarded (af_netlink.c:1946-1949),
 * after which NLMSG_OK fails and the next recv would block: it is an
 * environment failure here instead. It never happens with NETLINK_CAP_ACK
 * on the generic-netlink socket (every ack is 36 bytes) and chunks of at
 * most NLMSG_GOODSIZE. `id` NULL: no fail() (the best-effort teardown). */
static ssize_t nl_recv(const char *id, int index, int fd, int flags)
{
    struct iovec iov = {nl_buffer, sizeof(nl_buffer)};
    struct msghdr msg = {.msg_iov = &iov, .msg_iovlen = 1};
    ssize_t n = recvmsg(fd, &msg, flags);
    if (n < 0) return -errno;
    if (msg.msg_flags & MSG_TRUNC) {
        if (id) fail(id, index, "environment_failure", "netlink_truncated");
        return -EMSGSIZE;
    }
    return n;
}

static int nl_send(int fd, unsigned short type, unsigned short flags, unsigned char cmd,
                   const unsigned char *payload, size_t len, int genl)
{
    static unsigned char message[sizeof(struct nlmsghdr) + GENL_HDRLEN + MAX_PAYLOAD];
    struct nlmsghdr *header = (struct nlmsghdr *)message;
    size_t offset = NLMSG_HDRLEN;
    memset(message, 0, sizeof(message));
    if (genl) {
        struct genlmsghdr *g = (struct genlmsghdr *)(message + offset);
        g->cmd = cmd;
        g->version = WG_GENL_VERSION;  /* 1, which the controller also accepts */
        offset += GENL_HDRLEN;
    }
    memcpy(message + offset, payload, len);
    header->nlmsg_len = offset + len;
    header->nlmsg_type = type;
    header->nlmsg_flags = flags;
    header->nlmsg_seq = 1;
    return send(fd, message, header->nlmsg_len, 0) == (ssize_t)header->nlmsg_len ? 0 : -errno;
}

/* Receive until the acknowledgement (or NLMSG_DONE for a dump). Each data
 * message's attribute payload after `skip` bytes is appended as hex to `out`
 * when it is non-NULL. Returns the kernel's error code (0 on success). */
static int nl_receive(const char *id, int index, int fd, size_t skip, char *out, size_t out_size)
{
    size_t used = 0;
    if (out) { out[0] = 0; }
    int first = 1;
    for (;;) {
        ssize_t n = nl_recv(id, index, fd, 0);
        if (n < 0) return (int)n;
        for (struct nlmsghdr *h = (struct nlmsghdr *)nl_buffer; NLMSG_OK(h, n); h = NLMSG_NEXT(h, n)) {
            if (h->nlmsg_type == NLMSG_ERROR) return ((struct nlmsgerr *)NLMSG_DATA(h))->error;
            if (h->nlmsg_type == NLMSG_DONE) {
                int error = *(int *)NLMSG_DATA(h);
                return error;
            }
            if (out) {
                size_t len = h->nlmsg_len - NLMSG_HDRLEN - skip;
                if (used + 2 * len + 4 >= out_size) return -EMSGSIZE;
                used += (size_t)sprintf(out + used, "%s\"", first ? "" : ",");
                const unsigned char *data = (const unsigned char *)NLMSG_DATA(h) + skip;
                for (size_t k = 0; k < len; ++k) used += (size_t)sprintf(out + used, "%02x", data[k]);
                used += (size_t)sprintf(out + used, "\"");
                first = 0;
            }
        }
    }
}

static void attr(unsigned char *buf, size_t *len, unsigned short type, const void *data, size_t size)
{
    struct nlattr *a = (struct nlattr *)(buf + *len);
    a->nla_len = NLA_HDRLEN + size;
    a->nla_type = type;
    memcpy(buf + *len + NLA_HDRLEN, data, size);
    *len += NLA_ALIGN(a->nla_len);
}

/* The RTM_NEWLINK body that creates wg0 (the fixture's and wg_create's):
 * ifi_index 0, ifi_flags 0, IFLA_IFNAME "wg0", IFLA_LINKINFO/IFLA_INFO_KIND
 * "wireguard"; sent with NLM_F_CREATE | NLM_F_EXCL | NLM_F_ACK. */
#define NEWLINK_FLAGS (NLM_F_REQUEST | NLM_F_ACK | NLM_F_CREATE | NLM_F_EXCL)
static size_t newlink_wg0(unsigned char *payload, size_t size)
{
    size_t len = sizeof(struct ifinfomsg);
    memset(payload, 0, size);
    attr(payload, &len, IFLA_IFNAME, "wg0", 4);
    size_t linkinfo = len;
    attr(payload, &len, IFLA_LINKINFO | NLA_F_NESTED, "", 0);
    attr(payload, &len, IFLA_INFO_KIND, "wireguard", 10);
    ((struct nlattr *)(payload + linkinfo))->nla_len = len - linkinfo;
    return len;
}

/* The RTM_DELLINK body that deletes wg0 by name (the teardown's and
 * wg_delete's); sent with NLM_F_ACK. */
static size_t dellink_wg0(unsigned char *payload, size_t size)
{
    size_t len = sizeof(struct ifinfomsg);
    memset(payload, 0, size);
    attr(payload, &len, IFLA_IFNAME, "wg0", 4);
    return len;
}

/* L (docs/2026-10-05-l-lifecycle.md section 6): whether wg0 exists in this
 * trace process's namespace, its ifindex (resolved after each creation), and
 * whether the next successful up is the first since this device instance was
 * created (`route_into_wg0`). */
static int wg_exists;
static unsigned wg_ifindex;
static int first_up;
/* W9 (docs/2026-10-06-w8-w9-netns-routing.md 4.3): a `wg_deladdr 4` removed
 * wg0's IPv4 address since the last successful up, so the next up's add is
 * expected to succeed instead of failing EEXIST (L's rule, refined). */
static int addr4_deleted;

/* W9: the RTM_DELADDR body of wg0's fixture address and the RTM_DELROUTE
 * body of the default route via wg0, for one family: the messages
 * route_into_wg0 adds, deleted (sent with NLM_F_ACK; the acknowledgement's
 * error code is the operation's result: EADDRNOTAVAIL, ESRCH when absent). */
static size_t deladdr_wg0(int family, unsigned char *payload, size_t size)
{
    size_t len = sizeof(struct ifaddrmsg);
    memset(payload, 0, size);
    struct ifaddrmsg *ifa = (struct ifaddrmsg *)payload;
    ifa->ifa_family = family;
    ifa->ifa_index = wg_ifindex;
    if (family == AF_INET) {
        unsigned char a4[4] = {10, 255, 254, 1};
        ifa->ifa_prefixlen = 32;
        attr(payload, &len, IFA_LOCAL, a4, 4);
        attr(payload, &len, IFA_ADDRESS, a4, 4);
    } else {
        unsigned char a6[16] = {0xfd, 0, 0xff, 0xff, [15] = 1};
        ifa->ifa_prefixlen = 128;
        attr(payload, &len, IFA_ADDRESS, a6, 16);
    }
    return len;
}

static size_t delroute_wg0(int family, unsigned char *payload, size_t size)
{
    size_t len = sizeof(struct rtmsg);
    memset(payload, 0, size);
    struct rtmsg *rt = (struct rtmsg *)payload;
    uint32_t wg = wg_ifindex;
    rt->rtm_family = family;
    rt->rtm_table = RT_TABLE_MAIN;
    rt->rtm_protocol = RTPROT_STATIC;
    rt->rtm_scope = RT_SCOPE_LINK;
    rt->rtm_type = RTN_UNICAST;
    attr(payload, &len, RTA_OIF, &wg, sizeof(wg));
    return len;
}

/* W5 (docs/2026-10-06-w5-w6-receive.md, section 6; D2 [USER 2026-10-07]):
 * the network namespace's sysctls, set to 0 and read back for the
 * LEANUX_FIXTURE row (harness/linux.py EXPECTED_NET_FIXTURE). */
static long net_sysctl[3];
static const char *const NET_SYSCTLS[3] = {"/proc/sys/net/ipv6/auto_flowlabels", "/proc/sys/net/ipv4/icmp_ratelimit",
                                           "/proc/sys/net/ipv6/icmp/ratelimit"};
/* The link-local address on lo (W5, 2.5): the scoped-source injections.
 * fe80::ffff:1, not fe80::1: existing traces transmit to fe80::1 through wg0
 * (b1_trie_routing, wg_trie_v6, the generator), which a local address would
 * intercept [AGENT, W5+W6 fork]. */
static const unsigned char LO_LINK_LOCAL[16] = {0xfe, 0x80, [12] = 0xff, [13] = 0xff, [15] = 1};

static void set_net_sysctls(const char *id)
{
    for (int k = 0; k < 3; ++k) {
        FILE *f = fopen(NET_SYSCTLS[k], "w");
        if (!f || fputs("0\n", f) < 0 || fclose(f)) fail(id, -1, "environment_failure", "sysctl_write");
        f = fopen(NET_SYSCTLS[k], "r");
        if (!f || fscanf(f, "%ld", &net_sysctl[k]) != 1) fail(id, -1, "environment_failure", "sysctl_read");
        fclose(f);
    }
}

/* Fresh network namespace with `lo` up and, unless the trace asks for the
 * bare fixture, a down `wg0`, created over a temporary rtnetlink socket that
 * is closed again before the fixture descriptors are opened, so the
 * descriptor-table history matches the plain fixture. */
static void network_fixture(const char *id, int mode)
{
    if (unshare(CLONE_NEWNET)) fail(id, -1, "environment_failure", "unshare_net");
    net_live = 1;
    int rtnl = socket(AF_NETLINK, SOCK_RAW | SOCK_CLOEXEC, NETLINK_ROUTE);
    if (rtnl < 0) fail(id, -1, "environment_failure", "rtnetlink_socket");
    unsigned char payload[256];
    /* lo up: what wg0 sends to 127.0.0.1 and ::1 reaches the listeners. */
    struct ifinfomsg up = {.ifi_family = AF_UNSPEC, .ifi_index = 1, .ifi_flags = IFF_UP, .ifi_change = IFF_UP};
    if (mode == 3) {
        /* W8 (section 3.1): this namespace is D, the device's; C, the
         * creating one, is a second unshare, lo up as well; wg0 is created
         * over a rtnetlink socket in C with IFLA_NET_NS_FD naming D, so
         * rtnl_newlink_create registers the device in D (ifindex 3) and
         * wg_newlink sees src_net = C: creating_net = C. Both namespaces
         * stay parked at high descriptors for execute's socket setup. */
        if (nl_send(rtnl, RTM_NEWLINK, NLM_F_REQUEST | NLM_F_ACK, 0, (unsigned char *)&up, sizeof(up), 0) ||
            nl_receive(id, -1, rtnl, 0, NULL, 0))
            fail(id, -1, "environment_failure", "lo_up");
        if (close(rtnl)) fail(id, -1, "environment_failure", "close_rtnetlink");
        int d = open("/proc/self/ns/net", O_RDONLY);
        if (d < 0 || dup2(d, PARK_D_FD) != PARK_D_FD || close(d)) fail(id, -1, "environment_failure", "park_netns_d");
        if (unshare(CLONE_NEWNET)) fail(id, -1, "environment_failure", "unshare_net_c");
        rtnl = socket(AF_NETLINK, SOCK_RAW | SOCK_CLOEXEC, NETLINK_ROUTE);
        if (rtnl < 0) fail(id, -1, "environment_failure", "rtnetlink_socket_c");
        if (nl_send(rtnl, RTM_NEWLINK, NLM_F_REQUEST | NLM_F_ACK, 0, (unsigned char *)&up, sizeof(up), 0) ||
            nl_receive(id, -1, rtnl, 0, NULL, 0))
            fail(id, -1, "environment_failure", "lo_up_c");
        size_t len = newlink_wg0(payload, sizeof(payload));
        uint32_t ns_fd = PARK_D_FD;
        attr(payload, &len, IFLA_NET_NS_FD, &ns_fd, sizeof(ns_fd));
        if (nl_send(rtnl, RTM_NEWLINK, NEWLINK_FLAGS, 0, payload, len, 0) || nl_receive(id, -1, rtnl, 0, NULL, 0))
            fail(id, -1, "environment_failure", "create_wg0_in_d");
        wg_exists = 1;
        first_up = 1;
        if (close(rtnl)) fail(id, -1, "environment_failure", "close_rtnetlink_c");
        int c = open("/proc/self/ns/net", O_RDONLY);
        if (c < 0 || dup2(c, PARK_C_FD) != PARK_C_FD || close(c)) fail(id, -1, "environment_failure", "park_netns_c");
        if (setns(PARK_D_FD, CLONE_NEWNET)) fail(id, -1, "environment_failure", "setns_d");
        return;
    }
    if (mode != 2) {
        size_t len = newlink_wg0(payload, sizeof(payload));
        if (nl_send(rtnl, RTM_NEWLINK, NEWLINK_FLAGS, 0, payload, len, 0) || nl_receive(id, -1, rtnl, 0, NULL, 0))
            fail(id, -1, "environment_failure", "create_wg0");
        wg_exists = 1;
        first_up = 1;
    }
    if (nl_send(rtnl, RTM_NEWLINK, NLM_F_REQUEST | NLM_F_ACK, 0, (unsigned char *)&up, sizeof(up), 0) ||
        nl_receive(id, -1, rtnl, 0, NULL, 0))
        fail(id, -1, "environment_failure", "lo_up");
    /* W5: fe80::ffff:1/128 on lo (no DAD on IFF_LOOPBACK), for the link-local
     * sender; and the namespace's sysctls. */
    size_t len = sizeof(struct ifaddrmsg);
    memset(payload, 0, sizeof(payload));
    struct ifaddrmsg *ifa = (struct ifaddrmsg *)payload;
    ifa->ifa_family = AF_INET6;
    ifa->ifa_index = 1;
    /* /128, not /64: a prefix route fe80::/64 on lo would take every
     * link-local destination away from the default route via wg0 (the
     * first run sent b1_trie_routing's fe80::1 datagram out on lo). */
    ifa->ifa_prefixlen = 128;
    ifa->ifa_flags = IFA_F_NODAD;
    ifa->ifa_scope = RT_SCOPE_LINK;
    attr(payload, &len, IFA_ADDRESS, LO_LINK_LOCAL, 16);
    if (nl_send(rtnl, RTM_NEWADDR, NLM_F_REQUEST | NLM_F_CREATE | NLM_F_EXCL | NLM_F_ACK, 0, payload, len, 0) ||
        nl_receive(id, -1, rtnl, 0, NULL, 0))
        fail(id, -1, "environment_failure", "lo_link_local");
    if (close(rtnl)) fail(id, -1, "environment_failure", "close_rtnetlink");
    set_net_sysctls(id);
}

/* The inter-trace boundary (choice-stream strategy, section 4.4): delete wg0
 * synchronously at the end of a network trace, while the parent still holds
 * the armed remote instance. wg_destruct runs in this task (the device's
 * priv_destructor, run by rtnl_unlock), so the device's workqueues are
 * destroyed and its peers' timers stopped before the next trace exists. */
static void delete_wg0(const char *id)
{
    /* L: a trace may have deleted wg0 (or never created it). */
    if (!wg_exists) return;
    int rtnl = socket(AF_NETLINK, SOCK_RAW | SOCK_CLOEXEC, NETLINK_ROUTE);
    if (rtnl < 0) fail(id, -1, "environment_failure", "rtnetlink_socket_teardown");
    unsigned char payload[64];
    size_t len = dellink_wg0(payload, sizeof(payload));
    if (nl_send(rtnl, RTM_DELLINK, NLM_F_REQUEST | NLM_F_ACK, 0, payload, len, 0) || nl_receive(id, -1, rtnl, 0, NULL, 0))
        fail(id, -1, "environment_failure", "delete_wg0");
    wg_exists = 0;
    if (close(rtnl)) fail(id, -1, "environment_failure", "close_rtnetlink_teardown");
}

/* fail()'s teardown (audit M1): the same synchronous RTM_DELLINK, whatever
 * this process believes about wg0, with every error ignored (ENODEV when
 * there is none) and without calling fail(). */
static void delete_wg0_best_effort(void)
{
    int rtnl = socket(AF_NETLINK, SOCK_RAW | SOCK_CLOEXEC, NETLINK_ROUTE);
    if (rtnl < 0) return;
    unsigned char payload[64];
    size_t len = dellink_wg0(payload, sizeof(payload));
    if (!nl_send(rtnl, RTM_DELLINK, NLM_F_REQUEST | NLM_F_ACK, 0, payload, len, 0)) (void)nl_receive(NULL, -1, rtnl, 0, NULL, 0);
    close(rtnl);
}

static void resolve_wireguard_family(const char *id, int fd)
{
    unsigned char payload[64];
    size_t len = 0;
    attr(payload, &len, CTRL_ATTR_FAMILY_NAME, WG_GENL_NAME, sizeof(WG_GENL_NAME));
    if (nl_send(fd, GENL_ID_CTRL, NLM_F_REQUEST, CTRL_CMD_GETFAMILY, payload, len, 2))
        fail(id, -1, "environment_failure", "genl_getfamily");
    ssize_t n = nl_recv(id, -1, fd, 0);
    struct nlmsghdr *h = (struct nlmsghdr *)nl_buffer;
    if (n < 0 || !NLMSG_OK(h, n) || h->nlmsg_type != GENL_ID_CTRL) fail(id, -1, "environment_failure", "genl_family_reply");
    unsigned char *attrs = (unsigned char *)NLMSG_DATA(h) + GENL_HDRLEN;
    size_t remaining = h->nlmsg_len - NLMSG_HDRLEN - GENL_HDRLEN;
    while (remaining >= NLA_HDRLEN) {
        struct nlattr *a = (struct nlattr *)attrs;
        if (a->nla_len < NLA_HDRLEN || a->nla_len > remaining) break;
        if ((a->nla_type & NLA_TYPE_MASK) == CTRL_ATTR_FAMILY_ID) {
            memcpy(&wg_family, attrs + NLA_HDRLEN, sizeof(wg_family));
            return;
        }
        size_t step = (size_t)NLA_ALIGN(a->nla_len);
        remaining -= step < remaining ? step : remaining;
        attrs += NLA_ALIGN(a->nla_len);
    }
    fail(id, -1, "environment_failure", "genl_family_id");
}

static char dump_hex[2 * (1 << 16) * 4];

/* A descriptor argument: kind 0 a literal; 1 the result of an earlier
 * eventfd2/dup/dup3; 2 and 3 the read end (fd[0]) and write end (fd[1]) of an
 * earlier pipe2. A failed producer resolves to -1. Anything else is invalid
 * wire input (harness/trace.py never produces it). */
static long resolve(const struct trace *t, unsigned kind, long long value, const struct observation *results, unsigned i)
{
    if (!kind) return (long)(int32_t)value;
    if (kind > 3 || value < 0 || (unsigned long long)value >= i) fail(t->id, i, "invalid_input", "wire_descriptor");
    if ((kind == 1) == (t->ops[value].code == OP_PIPE2)) fail(t->id, i, "invalid_input", "wire_descriptor_producer");
    if (kind == 1) return results[value].ret >= 0 ? results[value].ret : -1;
    return results[value].ret == 0 ? results[value].fds[kind - 2] : -1;
}

/* The write buffer of operation i (P design section 6; Leanux/Runner.lean
 * writeBuffer): bytes 0-7 are the value little-endian, byte k >= 8 is
 * (7 i + 13 k + 17 (k >> 8)) mod 256. */
static void fill_write_buffer(unsigned i, uint64_t value, unsigned count)
{
    for (unsigned k = 0; k < 8; ++k) write_buffer[k] = (unsigned char)(value >> (8 * k));
    for (unsigned k = 8; k < count && k < MAX_IO; ++k) write_buffer[k] = (unsigned char)((7 * i + 13 * k + 17 * (k >> 8)) % 256);
}

static void print_hex_bytes(const unsigned char *data, long n)
{
    for (long k = 0; k < n; ++k) printf("%02x", data[k]);
}

/* An operation's observation fields beyond ret and errno: a read's head as
 * hex ("bytes") and its digest; a write's sigpipe; a pipe2's fds. The
 * comparison child prints the same values per field (LEANUX_CMP_RESULT). */
static void print_head(const struct operation *op, const struct observation *r)
{
    printf("\"");
    if (op->code == OP_READ && r->ret > 0) print_hex_bytes(r->bytes, r->ret < READ_HEAD ? r->ret : READ_HEAD);
    printf("\"");
}

static void print_digest(const struct operation *op, const struct observation *r)
{
    if (op->code != OP_READ || r->ret <= 0) { printf("null"); return; }
    printf("\"");
    print_hex_bytes(r->digest, 32);
    printf("\"");
}

static void print_fds(const struct operation *op, const struct observation *r)
{
    if (op->code == OP_PIPE2 && r->ret == 0) printf("[%d,%d]", r->fds[0], r->fds[1]); else printf("null");
}

/* comparisons: 0 records PCs (KCOV_TRACE_PC); 1 records comparison operands
 * (KCOV_TRACE_CMP) in a second, independent child for the same trace. */
/* Records are (type, arg1, arg2, ip). Each distinct record is printed once,
 * at its first occurrence, in execution order. */
static void print_records(const char *tag, const char *id, unsigned i, const unsigned long *area, unsigned long count,
                          const unsigned short *blocks)
{
    dedup_begin();
    unsigned long n = 0, nranges = 0;
    printf("%s {\"id\":\"%s\",\"index\":%u,\"count\":%lu,\"records\":[", tag, id, i, count);
    int comma = 0;
    for (unsigned long k = 0; k < count; ++k) {
        const unsigned long *r = area + 1 + 4 * k;
        unsigned long h = hash_words(r, 4) & DEDUP_MASK;
        for (; dedup_at(h); h = (h + 1) & DEDUP_MASK)
            if (!memcmp(area + 1 + 4 * (unsigned long)distinct[dedup_at(h) - 1].position, r, 4 * sizeof(*r))) break;
        unsigned d;
        if (dedup_at(h)) {
            d = dedup_at(h) - 1;
            if (!blocks) continue;
        } else {
            if (n >= DEDUP_SLOTS / 2) fail(id, (int)i, "coverage_failure", "dedup_table_full");
            d = (unsigned)n++;
            distinct[d] = (struct distinct_record){ .position = (unsigned)k, .head = 0, .tail = 0, .zero = 0 };
            dedup_set(h, d + 1);
            if (!blocks) {
                /* the task area: each distinct record once, in first-execution order */
                printf("%s[%lu,\"0x%lx\",\"0x%lx\",\"0x%lx\"]", comma ? "," : "", r[0], r[1], r[2], r[3]);
                comma = 1;
                continue;
            }
        }
        /* the remote area: the record's blocks as ranges, in area order
         * (split_hidden numbers blocks in area order, so a record's non-zero
         * blocks never decrease; a decrease is a fixture defect) */
        unsigned short b = blocks[k];
        if (!b) { distinct[d].zero = 1; continue; }
        if (distinct[d].tail) {
            struct block_range *t = &ranges[distinct[d].tail - 1];
            if (b < t->hi) fail(id, (int)i, "coverage_failure", "blocks_out_of_order");
            if (b <= t->hi + 1) { t->hi = b; continue; }
        }
        if (nranges >= CAPACITY / 4) fail(id, (int)i, "coverage_failure", "range_pool_full");
        ranges[nranges] = (struct block_range){ .lo = b, .hi = b, .next = 0 };
        if (distinct[d].tail) ranges[distinct[d].tail - 1].next = (unsigned)(nranges + 1);
        else distinct[d].head = (unsigned)(nranges + 1);
        distinct[d].tail = (unsigned)(++nranges);
    }
    if (blocks) {
        /* the remote area: each distinct record once, in sorted order, with
         * the blocks it occurred in as a fifth element ("1-3,7": ranges of
         * block numbers), so that a record repeated in every NET_RX section
         * of a flood costs one line, not one per section; the sort is over
         * the distinct records only */
        sort_area = area;
        qsort(distinct, n, sizeof(*distinct), compare_distinct);
        for (unsigned long d = 0; d < n; ++d) {
            const unsigned long *r = area + 1 + 4 * (unsigned long)distinct[d].position;
            printf("%s[%lu,\"0x%lx\",\"0x%lx\",\"0x%lx\",\"", comma ? "," : "", r[0], r[1], r[2], r[3]);
            int first_range = 1;
            unsigned next = distinct[d].head;
            if (distinct[d].zero) {
                /* block 0 sorts first and joins a range that starts at 1 */
                if (next && ranges[next - 1].lo == 1) {
                    printf("0-%u", ranges[next - 1].hi);
                    next = ranges[next - 1].next;
                } else printf("0");
                first_range = 0;
            }
            for (; next; next = ranges[next - 1].next) {
                const struct block_range *g = &ranges[next - 1];
                if (g->lo == g->hi) printf("%s%u", first_range ? "" : ",", g->lo);
                else printf("%s%u-%u", first_range ? "" : ",", g->lo, g->hi);
                first_range = 0;
            }
            printf("\"]");
            comma = 1;
        }
    }
    printf("]}\n");
}

/* Choices (docs/2026-10-03-choice-stream-strategy.md): the patched kernel's
 * kcov_choice_ip() writes tagged records into the KCOV area at generic
 * interception points (random draws, clock reads). They are split out
 * before deduplication and printed in area order as
 * [kind, call site, sequence number, length, value hex]; the area is
 * compacted in place to the ordinary entries and the new count returned.
 * A malformed record fails. */
#define CHOICE_MAGIC 0x4c5aUL
static void print_choice(int *comma, unsigned long kind, unsigned long ip, unsigned long seq, unsigned long len,
                         const unsigned long *words, unsigned long nwords)
{
    printf("%s[%lu,\"0x%lx\",%lu,%lu,\"", *comma ? "," : "", kind, ip, seq, len);
    unsigned long bytes = len < 8 * nwords ? len : 8 * nwords;
    for (unsigned long k = 0; k < bytes; ++k) printf("%02lx", (words[k / 8] >> (8 * (k % 8))) & 0xff);
    printf("\"]");
    *comma = 1;
}

static unsigned long split_hidden(const char *tag, const struct trace *t, unsigned i, unsigned long *area,
                                  unsigned long count, int comparisons)
{
    printf("%s {\"id\":\"%s\",\"index\":%u,\"mode\":\"%s\",\"records\":[", tag, t->id, i,
           comparisons ? "cmp" : "pc");
    unsigned long kept = 0;
    int comma = 0;
    if (!comparisons) {
        for (unsigned long j = 1; j <= count;) {
            unsigned long w = area[j];
            if (w >> 48 != CHOICE_MAGIC) { area[1 + kept++] = w; ++j; continue; }
            unsigned long n = w & 0xffff;
            if (n > 5 || j + 2 + n > count) fail(t->id, i, "coverage_failure", "malformed_choice_record");
            print_choice(&comma, (w >> 16) & 0xffff, area[j + 1], area[j + 2], (w >> 32) & 0xffff, area + j + 3, n);
            j += 3 + n;
        }
    } else {
        /* the dispatch-section block of each kept comparison record: a
         * section's records reach the remote area as one block at its stop,
         * start record first and stop record last, nested blocks before
         * their enclosing one, so a running count of start records numbers
         * the block and the stop record ends it (0 outside any block) */
        unsigned long block = 0, blocks = 0;
        for (unsigned long k = 0; k < count;) {
            unsigned long *r = area + 1 + 4 * k;
            if ((r[0] >> 63) && ((r[0] >> 32) & 0xffff) == CHOICE_MAGIC + 1)
                fail(t->id, i, "coverage_failure", "malformed_choice_record");   /* payload without header */
            if (!(r[0] >> 63) || ((r[0] >> 32) & 0xffff) != CHOICE_MAGIC) {
                if (kept != k) memmove(area + 1 + 4 * kept, r, 4 * sizeof(*r));
                cmp_block[kept] = (unsigned short)block;
                ++kept; ++k; continue;
            }
            unsigned long n = r[0] & 0xffff, nrec = 1 + (n + 2) / 3;
            unsigned long kind = (r[0] >> 16) & 0xffff;
            if (kind == 300) block = ++blocks;
            else if (kind == 301) block = 0;
            if (n > 5 || k + nrec > count) fail(t->id, i, "coverage_failure", "malformed_choice_record");
            unsigned long words[6] = {0};
            for (unsigned long w = 0; w < n; ++w) {
                const unsigned long *p = area + 1 + 4 * (k + 1 + w / 3);
                if (!(p[0] >> 63) || ((p[0] >> 32) & 0xffff) != CHOICE_MAGIC + 1 || (p[0] & 0xffff) != w / 3)
                    fail(t->id, i, "coverage_failure", "malformed_choice_record");
                words[w] = p[1 + w % 3];
            }
            print_choice(&comma, (r[0] >> 16) & 0xffff, r[1], r[2], r[3], words, n);
            k += nrec;
        }
    }
    printf("]}\n");
    return kept;
}

/* Deduplicate after capture, keeping each PC's first execution in order:
 * one pass over the area through the table (slots hold positions + 1). */
static void print_pcs(const char *tag, const char *id, unsigned i, const unsigned long *area, unsigned long count)
{
    dedup_begin();
    printf("%s {\"id\":\"%s\",\"index\":%u,\"count\":%lu,\"pcs\":[", tag, id, i, count);
    int comma = 0;
    unsigned long seen = 0;
    for (unsigned long j = 0; j < count; ++j) {
        unsigned long pc = area[j + 1], h = hash_words(&pc, 1) & DEDUP_MASK;
        for (; dedup_at(h); h = (h + 1) & DEDUP_MASK)
            if (area[dedup_at(h)] == pc) break;
        if (dedup_at(h)) continue;
        if (++seen > DEDUP_SLOTS / 2) fail(id, (int)i, "coverage_failure", "dedup_table_full");
        dedup_set(h, (unsigned)(j + 1));
        printf("%s\"0x%lx\"", comma ? "," : "", pc);
        comma = 1;
    }
    printf("]}\n");
}

static unsigned char observe_buffer[2048];
static struct timespec went_up;
/* the clock read before a candidate first up's window (becomes went_up) */
static struct timespec up_started;
static int up_seen;
/* the virtual time the trace's advances added to CLOCK_BOOTTIME */
static long long advanced_ns;
/* The trace's guest time from wg_up to its last operation's end (with that
 * operation's wait), net of the advances, reported per child: the margin to
 * REKEY_BOUND_NS. */
static long long since_up_ns;

static void print_hex(long n)
{
    for (long k = 0; k < n; ++k) printf("%02x", observe_buffer[k]);
}

/* W5: recvmsg into observe_buffer with the control messages the fixture
 * sockets are set to report: the TOS (IP_TOS, a byte) or traffic class
 * (IPV6_TCLASS, an int) into `tos` (-1 without one), and for the sender the
 * datagram's destination (IPV6_PKTINFO) into `dst` (zero for an IPv4
 * datagram). `source`, when given, receives the datagram's source. Returns
 * recvmsg's result (with MSG_TRUNC in `flags`, the real length). */
static long recv_with_cmsg(int fd, int flags, struct sockaddr_in6 *source, socklen_t *source_len, int *tos,
                           unsigned char dst[16])
{
    struct iovec iov = {.iov_base = observe_buffer, .iov_len = sizeof(observe_buffer)};
    union { struct cmsghdr h; unsigned char bytes[256]; } control;
    struct msghdr msg = {.msg_name = source, .msg_namelen = source ? *source_len : 0, .msg_iov = &iov, .msg_iovlen = 1,
                         .msg_control = &control, .msg_controllen = sizeof(control)};
    long n = recvmsg(fd, &msg, flags);
    if (n < 0) return n;
    if (source) *source_len = msg.msg_namelen;
    *tos = -1;
    if (dst) memset(dst, 0, 16);
    for (struct cmsghdr *c = CMSG_FIRSTHDR(&msg); c; c = CMSG_NXTHDR(&msg, c)) {
        if (c->cmsg_level == IPPROTO_IP && c->cmsg_type == IP_TOS) {
            *tos = *(unsigned char *)CMSG_DATA(c);
        } else if (c->cmsg_level == IPPROTO_IPV6 && c->cmsg_type == IPV6_TCLASS) {
            int v;
            memcpy(&v, CMSG_DATA(c), sizeof(v));
            *tos = v;
        } else if (c->cmsg_level == IPPROTO_IPV6 && c->cmsg_type == IPV6_PKTINFO && dst) {
            struct in6_pktinfo pi;
            memcpy(&pi, CMSG_DATA(c), sizeof(pi));
            memcpy(dst, &pi.ipi6_addr, 16);
        }
    }
    return n;
}

/* the TOS of the datagram wg_observe's own recvmsg returned (W5) */
static int first_tos = -1;

/* A datagram's (family, length, message type, TOS, bytes) as JSON; the
 * message type is the first little-endian u32 of a WireGuard message. */
static int print_datagram(int comma, int family, long n, int tos)
{
    unsigned type = n >= 4 ? (unsigned)observe_buffer[0] | (unsigned)observe_buffer[1] << 8 |
                             (unsigned)observe_buffer[2] << 16 | (unsigned)observe_buffer[3] << 24 : 0;
    printf("%s[%d,%ld,%u,%d,\"", comma ? "," : "", family, n, type, tos);
    print_hex(n);
    printf("\"]");
    return 1;
}

/* After wg_up, outside the coverage window: an address and a default route on
 * wg0 for each family, so the sender's datagrams reach wg_xmit. Routes need
 * the device up. The temporary socket is closed again. Temporary sockets in a
 * trace take the lowest free descriptor, and close() leaves its close-on-exec
 * bit as it was, so they are opened without SOCK_CLOEXEC: the bit stays clear,
 * as the mirror's descriptor table has it. */
static void rtnl_request(int rtnl, const char *id, unsigned index, unsigned short type, const void *body, size_t len,
                         const char *what, int expected)
{
    int error = nl_send(rtnl, type, NLM_F_REQUEST | NLM_F_ACK | NLM_F_CREATE | NLM_F_EXCL, 0, body, len, 0);
    if (!error) error = nl_receive(id, -1, rtnl, 0, NULL, 0);
    if (error != expected) {
        errno = error < 0 ? -error : 0;
        fail(id, index, "environment_failure", what);
    }
}

/* `first`: no successful up since this device instance was created (L,
 * docs/2026-10-05-l-lifecycle.md section 2.2 and 6). On a later up, wg0's
 * IPv4 address survived the down (only its routes were flushed) and must
 * be refused with EEXIST; the IPv6 address (keep_addr_on_down 0) and both
 * default routes were removed and must be added again. Any other outcome
 * fails the trace: the kernel's down behaviour is not the one modeled. */
static void route_into_wg0(const char *id, unsigned index, int first)
{
    int rtnl = socket(AF_NETLINK, SOCK_RAW, NETLINK_ROUTE);
    if (rtnl < 0) fail(id, index, "environment_failure", "route_socket");
    unsigned char body[128];
    uint32_t wg = wg_ifindex;
    /* W4 (design section 2.3): after an MTU change below a family's floor
     * the kernel has taken the family's IP device down (the inet6_dev below
     * 1280, addrconf.c:3691-3695; the in_device below 68, devinet.c:1637-1643)
     * and refuses the addresses and routes: the IPv6 address add is -EINVAL
     * (ipv6_add_dev, addrconf.c:381-382), the IPv4 address add -ENOBUFS
     * (devinet.c:888), the route adds -ENODEV. The refusals are expected
     * exactly; any other value fails the trace, as every request does. */
    struct ifreq mtu_request;
    memset(&mtu_request, 0, sizeof(mtu_request));
    strcpy(mtu_request.ifr_name, "wg0");
    if (ioctl(SEND_FD, SIOCGIFMTU, &mtu_request)) fail(id, index, "environment_failure", "get_wg0_mtu");
    int down4 = mtu_request.ifr_mtu < 68, down6 = mtu_request.ifr_mtu < 1280;
    for (int family = AF_INET; family; family = family == AF_INET ? AF_INET6 : 0) {
        int down = family == AF_INET ? down4 : down6;
        size_t len = sizeof(struct ifaddrmsg);
        memset(body, 0, sizeof(body));
        struct ifaddrmsg *ifa = (struct ifaddrmsg *)body;
        ifa->ifa_family = family;
        ifa->ifa_index = wg_ifindex;
        ifa->ifa_flags = IFA_F_NODAD;
        if (family == AF_INET) {
            unsigned char a4[4] = {10, 255, 254, 1};
            ifa->ifa_prefixlen = 32;
            attr(body, &len, IFA_LOCAL, a4, 4);
            attr(body, &len, IFA_ADDRESS, a4, 4);
        } else {
            unsigned char a6[16] = {0xfd, 0, 0xff, 0xff, [15] = 1};
            ifa->ifa_prefixlen = 128;
            attr(body, &len, IFA_ADDRESS, a6, 16);
        }
        rtnl_request(rtnl, id, index, RTM_NEWADDR, body, len,
                     first ? "address_on_wg0" : "address_on_wg0_after_down",
                     down ? (family == AF_INET ? -ENOBUFS : -EINVAL) : !first && family == AF_INET && !addr4_deleted ? -EEXIST : 0);   /* W9: unless deleted since */
        len = sizeof(struct rtmsg);
        memset(body, 0, sizeof(body));
        struct rtmsg *rt = (struct rtmsg *)body;
        rt->rtm_family = family;
        rt->rtm_table = RT_TABLE_MAIN;
        rt->rtm_protocol = RTPROT_STATIC;
        rt->rtm_scope = RT_SCOPE_LINK;
        rt->rtm_type = RTN_UNICAST;
        attr(body, &len, RTA_OIF, &wg, sizeof(wg));
        rtnl_request(rtnl, id, index, RTM_NEWROUTE, body, len,
                     first ? "default_route_via_wg0" : "default_route_via_wg0_after_down", down ? -ENODEV : 0);
        /* W4: the trace's host routes into wg0 with their MTU (RTAX_MTU), one
         * request each, after the default route of the family. */
        for (unsigned k = 0; k < n_fixture_routes; ++k) {
            const struct fixture_route *r = &fixture_routes[k];
            if ((int)(r->family == 4 ? AF_INET : AF_INET6) != family) continue;
            len = sizeof(struct rtmsg);
            memset(body, 0, sizeof(body));
            rt = (struct rtmsg *)body;
            rt->rtm_family = family;
            rt->rtm_dst_len = family == AF_INET ? 32 : 128;
            rt->rtm_table = RT_TABLE_MAIN;
            rt->rtm_protocol = RTPROT_STATIC;
            rt->rtm_scope = RT_SCOPE_LINK;
            rt->rtm_type = RTN_UNICAST;
            attr(body, &len, RTA_DST, r->dst, family == AF_INET ? 4 : 16);
            attr(body, &len, RTA_OIF, &wg, sizeof(wg));
            uint32_t mtu = r->mtu;
            unsigned char metrics[16];
            size_t mlen = 0;
            attr(metrics, &mlen, RTAX_MTU, &mtu, sizeof(mtu));
            attr(body, &len, RTA_METRICS, metrics, mlen);
            rtnl_request(rtnl, id, index, RTM_NEWROUTE, body, len,
                         first ? "fixture_route_via_wg0" : "fixture_route_via_wg0_after_down", down ? -ENODEV : 0);
        }
    }
    addr4_deleted = 0;   /* W9: the address is back */
    if (close(rtnl)) fail(id, index, "environment_failure", "route_close");
}

/* wg0's transmit counters and receive error counters over a temporary rtnetlink socket, which is closed
 * again (without SOCK_CLOEXEC, see route_into_wg0). The device is named,
 * not indexed (L: it may have been deleted or recreated); exactly ENODEV is
 * "no device", printed as `"stats":null`, and any other error fails. */
static void print_stats(const char *id, unsigned index)
{
    int rtnl = socket(AF_NETLINK, SOCK_RAW, NETLINK_ROUTE);
    if (rtnl < 0) fail(id, index, "environment_failure", "stats_socket");
    unsigned char request[64];
    size_t len = sizeof(struct ifinfomsg);
    memset(request, 0, sizeof(request));
    attr(request, &len, IFLA_IFNAME, "wg0", 4);
    if (nl_send(rtnl, RTM_GETLINK, NLM_F_REQUEST, 0, request, len, 0))
        fail(id, index, "environment_failure", "stats_request");
    ssize_t n = recv(rtnl, nl_buffer, sizeof(nl_buffer), 0);
    struct nlmsghdr *h = (struct nlmsghdr *)nl_buffer;
    if (n >= 0 && NLMSG_OK(h, n) && h->nlmsg_type == NLMSG_ERROR &&
        h->nlmsg_len >= NLMSG_LENGTH(sizeof(struct nlmsgerr)) &&
        ((struct nlmsgerr *)NLMSG_DATA(h))->error == -ENODEV) {
        printf("\"stats\":null");
        if (close(rtnl)) fail(id, index, "environment_failure", "stats_close");
        return;
    }
    if (n < 0 || !NLMSG_OK(h, n) || h->nlmsg_type != RTM_NEWLINK) fail(id, index, "environment_failure", "stats_reply");
    struct rtattr *a = IFLA_RTA(NLMSG_DATA(h));
    int remaining = (int)IFLA_PAYLOAD(h);
    const struct rtnl_link_stats64 *stats = NULL;
    for (; RTA_OK(a, remaining); a = RTA_NEXT(a, remaining))
        if (a->rta_type == IFLA_STATS64 && RTA_PAYLOAD(a) >= sizeof(*stats)) stats = RTA_DATA(a);
    if (!stats) fail(id, index, "environment_failure", "stats_missing");
    /* W5 (2.6): the device tstats (dev_get_tstats64): rx_packets and rx_bytes
     * count every honest data message and keepalive (update_rx_stats); the
     * driver never adds a transmit count, so tx_packets and tx_bytes stay 0. */
    printf("\"stats\":{\"tx_errors\":%llu,\"tx_dropped\":%llu,\"rx_frame_errors\":%llu,\"rx_length_errors\":%llu,"
           "\"rx_packets\":%llu,\"rx_bytes\":%llu,\"tx_packets\":%llu,\"tx_bytes\":%llu}",
           (unsigned long long)stats->tx_errors, (unsigned long long)stats->tx_dropped,
           (unsigned long long)stats->rx_frame_errors, (unsigned long long)stats->rx_length_errors,
           (unsigned long long)stats->rx_packets, (unsigned long long)stats->rx_bytes,
           (unsigned long long)stats->tx_packets, (unsigned long long)stats->tx_bytes);
    if (close(rtnl)) fail(id, index, "environment_failure", "stats_close");
}

/* After wg_observe's recvfrom: drain both listeners and read the counters.
 * The comparison-mode child does the same, so both children end in the same
 * state; only the PC-mode child reports. */
static void observe(const struct trace *t, unsigned i, long first, int comparisons)
{
    /* W8: after wg_netns_close the listeners and the injector are gone:
     * their datagrams are null (the first recvfrom returned -EBADF). */
    if (!comparisons) printf("LEANUX_WGOBS {\"id\":\"%s\",\"index\":%u,\"datagrams\":%s", t->id, i, netns_closed ? "null" : "[");
    int comma = 0;
    if (!netns_closed && first >= 0 && !comparisons) comma = print_datagram(comma, 4, first, first_tos);
    for (int family = 4; family <= 6 && !netns_closed; family += 2) {
        for (;;) {
            int tos;
            long n = recv_with_cmsg(family == 4 ? LISTEN4_FD : LISTEN6_FD, MSG_DONTWAIT, NULL, NULL, &tos, NULL);
            if (n < 0) {
                if (errno != EAGAIN) fail(t->id, i, "environment_failure", "drain_listener");
                break;
            }
            if (!comparisons) comma = print_datagram(comma, family, n, tos);
        }
    }
    if (!comparisons) printf("%s\"replies\":[", netns_closed ? "," : "],");
    /* What the sender received (wg0's datagrams to it, and inner packets
     * delivered to it): recvmsg's source as the IPv6 socket reports it
     * (family, address as hex, port, scope id; an IPv4 source appears
     * v4-mapped), the TOS / traffic class (W5), the destination
     * IPV6_PKTINFO reports (zero for an IPv4 datagram), then the length, the
     * WireGuard message type, the receiver index (bytes 8-11, little-endian)
     * and the bytes. */
    comma = 0;
    /* W8: the injector's inbox (wg0's datagrams to the outer sender in C)
     * before the inner sender's; both lists are sorted by the harness and
     * the mirror, so the order here does not matter. */
    for (int which = (t->net == 3 && !netns_closed) ? 0 : 1; which < 2; ++which) for (;;) {
        struct sockaddr_in6 source;
        socklen_t source_len = sizeof(source);
        memset(&source, 0, sizeof(source));
        int tos;
        unsigned char dst[16];
        long n = recv_with_cmsg(which ? SEND_FD : INJECT_FD, MSG_DONTWAIT | MSG_TRUNC, &source, &source_len, &tos, dst);
        if (n < 0) {
            if (errno != EAGAIN) fail(t->id, i, "environment_failure", "drain_sender");
            break;
        }
        if (n > (long)sizeof(observe_buffer)) fail(t->id, i, "environment_failure", "sender_datagram_truncated");
        if (source_len != sizeof(source)) fail(t->id, i, "environment_failure", "sender_source_length");
        if (comparisons) continue;
        unsigned type = n >= 4 ? (unsigned)observe_buffer[0] | (unsigned)observe_buffer[1] << 8 |
                                 (unsigned)observe_buffer[2] << 16 | (unsigned)observe_buffer[3] << 24 : 0;
        unsigned receiver = n >= 12 ? (unsigned)observe_buffer[8] | (unsigned)observe_buffer[9] << 8 |
                                      (unsigned)observe_buffer[10] << 16 | (unsigned)observe_buffer[11] << 24 : 0;
        printf("%s[%u,\"", comma ? "," : "", (unsigned)source.sin6_family);
        for (unsigned k = 0; k < sizeof(source.sin6_addr); ++k) printf("%02x", source.sin6_addr.s6_addr[k]);
        printf("\",%u,%u,%d,\"", (unsigned)ntohs(source.sin6_port), (unsigned)source.sin6_scope_id, tos);
        for (unsigned k = 0; k < 16; ++k) printf("%02x", dst[k]);
        printf("\",%ld,%u,%u,\"", n, type, receiver);
        print_hex(n);
        printf("\"]");
        comma = 1;
    }
    if (comparisons) return;
    printf("],");
    print_stats(t->id, i);
    printf("}\n");
}

/* wg0's ifindex, through the fixture's sender (dev_ioctl), after each
 * creation: 3 in the fixture's namespace (lo 1, sit0 2), 4 after a deletion
 * and a recreation; the dumps and the trace's results show it. */
static void resolve_wg_ifindex(const char *id, int index)
{
    struct ifreq request;
    memset(&request, 0, sizeof(request));
    strcpy(request.ifr_name, "wg0");
    if (ioctl(SEND_FD, SIOCGIFINDEX, &request) || request.ifr_ifindex <= 0)
        fail(id, index, "environment_failure", "wg0_ifindex");
    wg_ifindex = (unsigned)request.ifr_ifindex;
}

/* The temporary rtnetlink socket of wg_create and wg_delete (L, section 5):
 * opened before the operation's coverage window at the lowest free
 * descriptor, without SOCK_CLOEXEC (close() keeps the close-on-exec bit, and
 * the mirror's table has it clear), and closed after the window. */
static int rtnl_temporary(const struct trace *t, unsigned i)
{
    int fd = socket(AF_NETLINK, SOCK_RAW, NETLINK_ROUTE);
    if (fd < 0) fail(t->id, (int)i, "environment_failure", "lifecycle_rtnetlink_socket");
    return fd;
}

/* Remote coverage for network traces. KCOV_REMOTE_ENABLE claims the calling
 * task's KCOV slot (a later KCOV_ENABLE would fail with EBUSY), so this
 * process enables it and forks the process that runs the trace: fork passes
 * the common handle down (copy_process) but not the KCOV slot. This process
 * arms the instance with the dispatch set: while it is armed, the patched
 * kernel's process_one_work and NET_RX vector open a section under the
 * common handle for each dispatch of a function in the set, collecting into
 * this shared mapping. This process keeps the KCOV descriptor open, which
 * keeps the handle registered (and the instance armed), and waits; then it
 * reads the count of sections that could not open or lost records, and a
 * nonzero count fails the trace. */
static unsigned long *enable_remote(const struct trace *t, int comparisons)
{
    int fd = open("/sys/kernel/debug/kcov", O_RDWR);
    if (fd != 3) fail(t->id, -1, "coverage_failure", "open_remote_kcov_at_3");
    if (ioctl(fd, KCOV_INIT_TRACE, CAPACITY)) fail(t->id, -1, "coverage_failure", "initialize_remote_kcov");
    unsigned long *area = mmap(NULL, CAPACITY * sizeof(*area), PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    if (area == MAP_FAILED) fail(t->id, -1, "coverage_failure", "map_remote_kcov");
    struct kcov_remote_arg arg = {
        .trace_mode = comparisons ? KCOV_TRACE_CMP : KCOV_TRACE_PC, .area_size = CAPACITY, .num_handles = 0,
        .common_handle = kcov_remote_handle(KCOV_SUBSYSTEM_COMMON, (uint32_t)getpid()),
    };
    if (ioctl(fd, KCOV_REMOTE_ENABLE, &arg)) fail(t->id, -1, "coverage_failure", "enable_remote_kcov");
    /* A steering schedule is attached to this remote instance before the
     * trace process exists; its leftovers are read back after it exits. */
    if (t->nsteer) {
        static struct steer_arg steer;
        steer.n = t->nsteer;
        memcpy(steer.e, t->steer, t->nsteer * sizeof(steer.e[0]));
        if (ioctl(fd, KCOV_LEANUX_STEER_LOAD, &steer)) fail(t->id, -1, "coverage_failure", "load_steering");
    }
    if (!trace_dispatch.n) fail(t->id, -1, "invalid_input", "wire_dispatch");
    if (ioctl(fd, KCOV_LEANUX_DISPATCH_LOAD, &trace_dispatch)) fail(t->id, -1, "coverage_failure", "load_dispatch");
    fflush(stdout);   /* a bulk trace's buffered rows stay with this process */
    pid_t child = fork();
    if (child < 0) fail(t->id, -1, "environment_failure", "fork_trace");
    if (child) {
        int status;
        /* W8: only the trace process signals the batch */
        if (t->net == 3 && (close(PIN_SIGNAL_FD) || close(PIN_ACK_FD))) fail(t->id, -1, "environment_failure", "pin_sock_parent");
        if (waitpid(child, &status, 0) != child) fail(t->id, -1, "environment_failure", "wait_trace");
        if (t->nsteer) {
            uint32_t left[2];
            if (ioctl(fd, KCOV_LEANUX_STEER_STATUS, left)) fail(t->id, -1, "coverage_failure", "steering_status");
            printf("LEANUX_STEER {\"id\":\"%s\",\"mode\":\"%s\",\"remaining\":%u,\"mismatches\":%u}\n",
                   t->id, comparisons ? "cmp" : "pc", left[0], left[1]);
            fflush(stdout);
        }
        uint32_t sections[2];
        if (ioctl(fd, KCOV_LEANUX_SECTION_STATUS, sections)) fail(t->id, -1, "coverage_failure", "section_status");
        printf("LEANUX_SECTIONS {\"id\":\"%s\",\"mode\":\"%s\",\"dropped\":%u,\"opened\":%u}\n",
               t->id, comparisons ? "cmp" : "pc", sections[0], sections[1]);
        fflush(stdout);
        if (sections[0]) fail(t->id, -1, "coverage_failure", "dropped_sections");
        _exit(WIFEXITED(status) ? WEXITSTATUS(status) : 1);
    }
    /* The trace process: the mapping stays, the descriptor goes. */
    if (close(fd)) fail(t->id, -1, "environment_failure", "close_remote_kcov");
    return area;
}

/* A2: a trace without a remote instance (an FS trace) loads its steering
 * schedule on its own KCOV descriptor, before KCOV_ENABLE; the patched kernel
 * consults a task instance's schedule in the task's own context. The trace
 * process reads the leftovers back itself, after its last operation. */
static void load_task_steering(const struct trace *t, int coverage_fd)
{
    static struct steer_arg steer;
    if (t->net || !t->nsteer) return;
    steer.n = t->nsteer;
    memcpy(steer.e, t->steer, t->nsteer * sizeof(steer.e[0]));
    if (ioctl(coverage_fd, KCOV_LEANUX_STEER_LOAD, &steer)) fail(t->id, -1, "coverage_failure", "load_steering");
}

static void task_steering_status(const struct trace *t, int coverage_fd, int comparisons)
{
    uint32_t left[2];
    if (t->net || !t->nsteer) return;
    if (ioctl(coverage_fd, KCOV_LEANUX_STEER_STATUS, left)) fail(t->id, -1, "coverage_failure", "steering_status");
    printf("LEANUX_STEER {\"id\":\"%s\",\"mode\":\"%s\",\"remaining\":%u,\"mismatches\":%u}\n",
           t->id, comparisons ? "cmp" : "pc", left[0], left[1]);
    fflush(stdout);
}

/* An armed trace's allocation records and unwinds (A0's cost measure). */
static void alloc_status(const struct trace *t, int coverage_fd, int comparisons)
{
    struct { uint32_t records, unwinds; uint64_t cycles; } status;
    if (!alloc.n && !alloc.flags) return;
    if (ioctl(coverage_fd, KCOV_LEANUX_ALLOC_STATUS, &status)) fail(t->id, -1, "coverage_failure", "allocation_status");
    printf("LEANUX_ALLOC {\"id\":\"%s\",\"mode\":\"%s\",\"records\":%u,\"unwinds\":%u,\"cycles\":%" PRIu64 "}\n",
           t->id, comparisons ? "cmp" : "pc", status.records, status.unwinds, status.cycles);
    fflush(stdout);
}

/* E-B (docs/2026-10-05-e-dos.md §8, queue-depth design): an io_uring batch to
 * wg0's port, sent from the fixture sender (SEND_FD) so wg0's cookie replies
 * come back to a socket the fixture reads and make_cookie's source matches the
 * mirror's. The batch is `n_leading` valid-MAC1 initiations (processed first,
 * each under load via the queue depth -> one byte-exact cookie reply), then an
 * optional mid-flood `control` valid initiation (a negative control: the mirror
 * does not model it, so its cookie records land in the discarded region and the
 * check fails closed), then `n_invalid` invalid-MAC1 initiations. The batch has
 * no per-send cond_resched, so it outruns the single-CPU receive worker and the
 * whole batch is queued (handshake_queue_len = total >= 512) before the worker
 * runs (GSO/sendmmsg do not cross cheaply, measured). The invalid template has a
 * MAC1 that will not match, so invalid packets are dropped (reply-free). The
 * ring and SQEs are prepared before the coverage window (the ring's inode setup
 * draws clock records that are not WireGuard sites); only io_uring_enter runs in
 * the window, so the producer sections land in it. The payload is
 * n_leading(1) ‖ control_flag(1) ‖ (n_leading + control_flag) × 148-byte msgs. */
struct flood_state {
    int ring;
    void *sq;
    struct io_uring_sqe *sqes;
    size_t sqsz, sqesz;
    unsigned *ktail, submit;
    struct sockaddr_in6 dst;
    unsigned char tmpl[148];
};

static int flood_prep(struct flood_state *fs, unsigned port, unsigned n_invalid,
                      const unsigned char *payload, unsigned payload_len)
{
    memset(fs->tmpl, 0, sizeof(fs->tmpl));
    fs->tmpl[0] = 1;                       /* MESSAGE_HANDSHAKE_INITIATION */
    memset(fs->tmpl + 116, 0xff, 16);     /* a MAC1 that will not match */
    /* v4-mapped destination: SEND_FD is the dual-stack IPv6 fixture sender, so
     * wg0 sees IPv4 from 127.0.0.1:SENDER_PORT (as wg_inject does). */
    memset(&fs->dst, 0, sizeof(fs->dst));
    fs->dst.sin6_family = AF_INET6; fs->dst.sin6_port = htons((uint16_t)port);
    fs->dst.sin6_addr.s6_addr[10] = fs->dst.sin6_addr.s6_addr[11] = 0xff;
    fs->dst.sin6_addr.s6_addr[12] = 127; fs->dst.sin6_addr.s6_addr[15] = 1;
    unsigned n_leading = payload_len >= 2 ? payload[0] : 0;
    unsigned control = payload_len >= 2 ? payload[1] : 0;
    if ((unsigned)2 + (n_leading + control) * 148u != payload_len) return -1;
    unsigned total = n_leading + control + n_invalid;
    struct io_uring_params pp; memset(&pp, 0, sizeof(pp));
    fs->ring = syscall(SYS_io_uring_setup, total, &pp);
    if (fs->ring < 0) return -1;
    fs->sqsz = pp.sq_off.array + pp.sq_entries * sizeof(unsigned);
    fs->sqesz = pp.sq_entries * sizeof(struct io_uring_sqe);
    fs->sq = mmap(0, fs->sqsz, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, fs->ring, IORING_OFF_SQ_RING);
    fs->sqes = mmap(0, fs->sqesz, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, fs->ring, IORING_OFF_SQES);
    if (fs->sq == MAP_FAILED || fs->sqes == MAP_FAILED) { close(fs->ring); return -1; }
    fs->ktail = (unsigned *)((char *)fs->sq + pp.sq_off.tail);
    unsigned *karray = (unsigned *)((char *)fs->sq + pp.sq_off.array);
    unsigned mask = *(unsigned *)((char *)fs->sq + pp.sq_off.ring_mask);
    fs->submit = total < pp.sq_entries ? total : pp.sq_entries;
    for (unsigned i = 0; i < fs->submit; i++) {
        struct io_uring_sqe *e = &fs->sqes[i]; memset(e, 0, sizeof(*e));
        e->opcode = IORING_OP_SEND; e->fd = SEND_FD;
        e->addr2 = (unsigned long)&fs->dst; e->addr_len = sizeof(fs->dst);
        /* order: leading valids, then the control valid, then the invalids */
        if (i < n_leading + control) { e->addr = (unsigned long)(payload + 2 + i * 148u); e->len = 148; }
        else { e->addr = (unsigned long)fs->tmpl; e->len = sizeof(fs->tmpl); }
        karray[i & mask] = i;
    }
    return 0;
}

static int flood_enter(struct flood_state *fs)
{
    __atomic_store_n(fs->ktail, fs->submit, __ATOMIC_RELEASE);
    long r = syscall(SYS_io_uring_enter, fs->ring, fs->submit, 0, 0, 0, 0);
    return r < 0 ? -1 : 0;
}

static void flood_cleanup(struct flood_state *fs)
{
    munmap(fs->sqes, fs->sqesz);
    munmap(fs->sq, fs->sqsz);
    close(fs->ring);
}

/* W7 stream B (docs/2026-10-06-w4-w7-transmit-bulk.md, 5.5): wg_batch, one
 * io_uring_enter of up to BATCH_MAX sends from SEND_FD: injects to wg0's
 * port (v4-mapped 127.0.0.1 or ::1, as wg_inject) and transmits into wg0
 * (the 16-byte destination then the payload, as wg_xmit's wire), prepared
 * before the window as the flood is. The completions present when
 * io_uring_enter returns are the operation's cqes (LEANUX_WGBATCH, the PC
 * child): the send's result per item, or null. The wire payload is per item
 * kind(1: inject, 2: xmit) ‖ length(2, big-endian) ‖ body. */
#define BATCH_MAX 1025
struct batch_state {
    int ring;
    void *sq, *cq;
    struct io_uring_sqe *sqes;
    size_t sqsz, sqesz, cqsz;
    unsigned *ktail, submit, n;
    unsigned *cqhead, *cqtail, cqmask;
    struct io_uring_cqe *cqes;
    struct sockaddr_in6 dst[BATCH_MAX];
    long res[BATCH_MAX];
    unsigned char present[BATCH_MAX];
};
static struct batch_state batch;

static int batch_prep(struct batch_state *bs, const unsigned char *payload, size_t len)
{
    static const unsigned char *body[BATCH_MAX];
    static unsigned blen[BATCH_MAX];
    static unsigned char kind[BATCH_MAX];
    memset(bs, 0, sizeof(*bs));
    size_t pos = 0;
    unsigned n = 0;
    while (pos < len) {
        if (pos + 3 > len || n >= BATCH_MAX) return -1;
        unsigned k = payload[pos], l = ((unsigned)payload[pos + 1] << 8) | payload[pos + 2];
        if (pos + 3 + l > len) return -2;
        kind[n] = (unsigned char)k; body[n] = payload + pos + 3; blen[n] = l; n++;
        pos += 3 + l;
    }
    if (!n) return -3;
    struct io_uring_params pp; memset(&pp, 0, sizeof(pp));
    bs->ring = syscall(SYS_io_uring_setup, n, &pp);
    if (bs->ring < 0) return -4;
    if (n > pp.sq_entries) { close(bs->ring); return -5; }
    bs->sqsz = pp.sq_off.array + pp.sq_entries * sizeof(unsigned);
    bs->sqesz = pp.sq_entries * sizeof(struct io_uring_sqe);
    bs->cqsz = pp.cq_off.cqes + pp.cq_entries * sizeof(struct io_uring_cqe);
    bs->sq = mmap(0, bs->sqsz, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, bs->ring, IORING_OFF_SQ_RING);
    bs->sqes = mmap(0, bs->sqesz, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, bs->ring, IORING_OFF_SQES);
    bs->cq = mmap(0, bs->cqsz, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, bs->ring, IORING_OFF_CQ_RING);
    if (bs->sq == MAP_FAILED || bs->sqes == MAP_FAILED || bs->cq == MAP_FAILED) { close(bs->ring); return -6; }
    bs->ktail = (unsigned *)((char *)bs->sq + pp.sq_off.tail);
    unsigned *karray = (unsigned *)((char *)bs->sq + pp.sq_off.array);
    unsigned mask = *(unsigned *)((char *)bs->sq + pp.sq_off.ring_mask);
    bs->cqhead = (unsigned *)((char *)bs->cq + pp.cq_off.head);
    bs->cqtail = (unsigned *)((char *)bs->cq + pp.cq_off.tail);
    bs->cqmask = *(unsigned *)((char *)bs->cq + pp.cq_off.ring_mask);
    bs->cqes = (struct io_uring_cqe *)((char *)bs->cq + pp.cq_off.cqes);
    bs->submit = bs->n = n;
    for (unsigned i = 0; i < n; i++) {
        struct sockaddr_in6 *d = &bs->dst[i];
        memset(d, 0, sizeof(*d));
        d->sin6_family = AF_INET6;
        struct io_uring_sqe *e = &bs->sqes[i]; memset(e, 0, sizeof(*e));
        e->opcode = IORING_OP_SEND; e->fd = SEND_FD; e->user_data = i;
        e->addr2 = (unsigned long)d; e->addr_len = sizeof(*d);
        if (kind[i] == 1) {   /* inject: family(1) ‖ port(2) ‖ message */
            if (blen[i] < 4) return -7;
            unsigned family = body[i][0], port = ((unsigned)body[i][1] << 8) | body[i][2];
            d->sin6_port = htons((uint16_t)port);
            if (family == 4) {
                d->sin6_addr.s6_addr[10] = d->sin6_addr.s6_addr[11] = 0xff;
                d->sin6_addr.s6_addr[12] = 127; d->sin6_addr.s6_addr[15] = 1;
            } else d->sin6_addr.s6_addr[15] = 1;
            e->addr = (unsigned long)(body[i] + 3); e->len = blen[i] - 3;
        } else if (kind[i] == 2) {   /* xmit: the destination, then the payload */
            if (blen[i] <= sizeof(d->sin6_addr)) return -8;
            d->sin6_port = htons(SEND_PORT);
            memcpy(&d->sin6_addr, body[i], sizeof(d->sin6_addr));
            e->addr = (unsigned long)(body[i] + sizeof(d->sin6_addr)); e->len = blen[i] - sizeof(d->sin6_addr);
        } else return -9;
        karray[i & mask] = i;
    }
    return 0;
}

static long batch_enter(struct batch_state *bs)
{
    __atomic_store_n(bs->ktail, bs->submit, __ATOMIC_RELEASE);
    long r = syscall(SYS_io_uring_enter, bs->ring, bs->submit, 0, 0, 0, 0);
    int saved = errno;
    /* the completions present at the return, each at its item (user_data) */
    unsigned head = *bs->cqhead, tail = __atomic_load_n(bs->cqtail, __ATOMIC_ACQUIRE);
    while (head != tail) {
        struct io_uring_cqe *c = &bs->cqes[head & bs->cqmask];
        if (c->user_data < bs->n) { bs->res[c->user_data] = c->res; bs->present[c->user_data] = 1; }
        head++;
    }
    __atomic_store_n(bs->cqhead, head, __ATOMIC_RELEASE);
    errno = saved;
    return r;
}

static void batch_cleanup(struct batch_state *bs)
{
    munmap(bs->cq, bs->cqsz);
    munmap(bs->sqes, bs->sqesz);
    munmap(bs->sq, bs->sqsz);
    close(bs->ring);
}

/* W8: a settle of `us` microseconds inside a window, by CLOCK_MONOTONIC_COARSE
 * through the vDSO: no system call and no clocksource read, so the window
 * records nothing (a nanosleep arms an hrtimer: clock records from an
 * undeclared consumer; the coarse clock's vDSO path reads the tick's
 * timestamp whatever the clocksource, so it never falls back to the system
 * call under refined-jiffies). The coarse clock advances at the ticks, the
 * unit the RCU grace period is counted in; nothing depends on the TSC rate,
 * which a boot whose calibration failed reports as 0 in /proc/cpuinfo. */
static void settle_spin(const char *id, unsigned index, unsigned long long us)
{
    struct timespec start, now;
    if (clock_gettime(CLOCK_MONOTONIC_COARSE, &start)) fail(id, (int)index, "environment_failure", "settle_clock");
    do {
        __asm__ volatile("pause");
        if (clock_gettime(CLOCK_MONOTONIC_COARSE, &now)) fail(id, (int)index, "environment_failure", "settle_clock");
    } while ((now.tv_sec - start.tv_sec) * 1000000000LL + (now.tv_nsec - start.tv_nsec) < (long long)(us * 1000));
}

static void execute(const struct trace *t, int input_fd, int comparisons)
{
    fixture_routes = t->routes;   /* W4: for route_into_wg0 at every wg_up */
    n_fixture_routes = t->nroutes;
    struct observation result[MAX_OPS] = {{0}};
    if (close(input_fd)) fail(t->id, -1, "environment_failure", "close_input");
    /* W8: the pin handshake's ends, moved above every descriptor the trace
     * can see; every child drops the inherited originals (the batch's low
     * socket descriptors would otherwise shift the fixture). */
    if (t->net == 3 && (dup2(pin_sock[1], PIN_SIGNAL_FD) != PIN_SIGNAL_FD || dup2(pin_sock[2], PIN_ACK_FD) != PIN_ACK_FD))
        fail(t->id, -1, "environment_failure", "pin_sock_dup");
    for (int k = 0; k < 4; ++k)
        if (close(pin_sock[k])) fail(t->id, -1, "environment_failure", "pin_sock_close");
    /* W7 (probe P-A, section 12 of docs/2026-10-06-w4-w7-transmit-bulk.md):
     * a bulk trace's rows are held in memory and written after its last
     * operation. The serial console takes about 0.5 MB/s under TCG, and the
     * comparison child of a 1024-item batch prints about 2.4 MB for that
     * operation, which alone exceeds the 4.5 s rekey bound; the rows are
     * unchanged. A child the watchdog kills loses its unwritten rows
     * (fail() still writes its error row). */
    for (unsigned k = 0; k < t->count; ++k)
        if (t->ops[k].code == OP_WG_BATCH) {
            if (setvbuf(stdout, bulk_out, _IOFBF, sizeof bulk_out)) fail(t->id, -1, "environment_failure", "bulk_out");
            break;
        }
    /* The parent's watchdog: SIGALRM's handler is the parent's, not ours; and
     * this child leads its own process group, so the watchdog's kill reaches
     * a network trace's trace process too. */
    if (signal(SIGALRM, SIG_DFL) == SIG_ERR) fail(t->id, -1, "environment_failure", "reset_sigalrm");
    if (setpgid(0, 0)) fail(t->id, -1, "environment_failure", "setpgid");
    unsigned long *remote = t->net ? enable_remote(t, comparisons) : NULL;
    if (t->net) network_fixture(t->id, (int)t->net);
    if (t->net == 3) {
        /* W8 (section 3.2, C1): the batch pins D (/proc/<pid>/ns/net) until
         * it ends, so D's asynchronous teardown never runs while a later run
         * is armed with cleanup_net; it learns the pid once both namespaces
         * exist and answers before any window. */
        pid_t self = getpid();
        char ack = 0;
        if (write(PIN_SIGNAL_FD, &self, sizeof(self)) != (ssize_t)sizeof(self)) fail(t->id, -1, "environment_failure", "pin_signal");
        if (read(PIN_ACK_FD, &ack, 1) != 1 || ack != 'k') fail(t->id, -1, "environment_failure", "pin_ack");
        if (close(PIN_SIGNAL_FD) || close(PIN_ACK_FD)) fail(t->id, -1, "environment_failure", "pin_sock_done");
    }
    /* Init invokes us with exactly console descriptors 0, 1, and 2. */
    for (int fd = 0; fd < 3; ++fd)
        if (fcntl(fd, F_GETFD) < 0) fail(t->id, -1, "environment_failure", "console_layout");
    for (int fd = 3; fd < 32; ++fd)
        if (fcntl(fd, F_GETFD) >= 0 || errno != EBADF)
            fail(t->id, -1, "environment_failure", "unexpected_inherited_descriptor");
    int coverage_fd = open("/sys/kernel/debug/kcov", O_RDWR);
    if (coverage_fd != 3) fail(t->id, -1, "coverage_failure", "open_kcov_at_3");
    if (ioctl(coverage_fd, KCOV_INIT_TRACE, CAPACITY)) fail(t->id, -1, "coverage_failure", "initialize_kcov");
    if ((alloc.n || alloc.flags) && ioctl(coverage_fd, KCOV_LEANUX_ALLOC_LOAD, &alloc))
        fail(t->id, -1, "coverage_failure", "load_allocation_set");
    load_task_steering(t, coverage_fd);
    unsigned long *coverage = mmap(NULL, CAPACITY * sizeof(*coverage), PROT_READ | PROT_WRITE, MAP_SHARED, coverage_fd, 0);
    if (coverage == MAP_FAILED) fail(t->id, -1, "coverage_failure", "map_kcov");
    for (int fd = 4; fd < (t->net ? LISTEN4_FD : 8); ++fd)
        if (open("/dev/null", O_RDWR) != fd) fail(t->id, -1, "environment_failure", "fill_descriptor");
    if (t->net) {
        /* No SOCK_CLOEXEC or SOCK_NONBLOCK: every fixture descriptor keeps the
         * plain fixture's flags; reads that must not block use MSG_DONTWAIT. */
        struct sockaddr_in a4 = {.sin_family = AF_INET, .sin_port = htons(LISTEN_PORT)};
        a4.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
        struct sockaddr_in6 a6 = {.sin6_family = AF_INET6, .sin6_port = htons(LISTEN_PORT), .sin6_addr = IN6ADDR_LOOPBACK_INIT};
        int one = 1;
        /* W8: the listeners are C's (wg0 sends in C, and only a socket in C
         * receives). W5: every fixture socket reports the TOS / traffic class of
         * what it receives (recvmsg cmsg), the sender also the destination. */
        if (t->net == 3 && setns(PARK_C_FD, CLONE_NEWNET)) fail(t->id, -1, "environment_failure", "setns_c_listeners");
        /* W7 (design section 12): the bulk tiers deliver up to 1025 datagrams
         * to a listener in one operation; the default rmem (212992) holds about
         * 270 small ones, so both listeners take SO_RCVBUFFORCE 8 MiB (root). */
        int rcvbuf = 8 * 1024 * 1024;
        if (socket(AF_INET, SOCK_DGRAM, 0) != LISTEN4_FD || bind(LISTEN4_FD, (struct sockaddr *)&a4, sizeof(a4)) ||
            setsockopt(LISTEN4_FD, IPPROTO_IP, IP_RECVTOS, &one, sizeof(one)) ||
            setsockopt(LISTEN4_FD, SOL_SOCKET, SO_RCVBUFFORCE, &rcvbuf, sizeof(rcvbuf)))
            fail(t->id, -1, "environment_failure", "listener4_at_4");
        if (socket(AF_INET6, SOCK_DGRAM, 0) != LISTEN6_FD ||
            setsockopt(LISTEN6_FD, IPPROTO_IPV6, IPV6_V6ONLY, &one, sizeof(one)) ||
            setsockopt(LISTEN6_FD, IPPROTO_IPV6, IPV6_RECVTCLASS, &one, sizeof(one)) ||
            setsockopt(LISTEN6_FD, SOL_SOCKET, SO_RCVBUFFORCE, &rcvbuf, sizeof(rcvbuf)) ||
            bind(LISTEN6_FD, (struct sockaddr *)&a6, sizeof(a6)))
            fail(t->id, -1, "environment_failure", "listener6_at_5");
        int zero = 0;
        /* W8: the inner sender and the generic-netlink socket are D's */
        if (t->net == 3 && setns(PARK_D_FD, CLONE_NEWNET)) fail(t->id, -1, "environment_failure", "setns_d_sender");
        struct sockaddr_in6 from = {.sin6_family = AF_INET6, .sin6_port = htons(SENDER_PORT), .sin6_addr = IN6ADDR_ANY_INIT};
        /* D2: the IP packets the sender routes into wg0 are determined by
         * the trace (Env.xmitPacket, docs/2026-10-04-d2-data-plane.md section
         * 2). IP_PMTUDISC_DO sets DF and clears ignore_df, so an unconnected
         * socket's IPv4 id is 0 rather than drawn from the jiffies-based
         * ident generator; IPV6_AUTOFLOWLABEL = 0 keeps the flow label 0
         * rather than a hash under a boot-time secret. */
        int pmtudisc = IP_PMTUDISC_DO;
        /* W4 (design 2.7): a large send buffer, so a batch of sends is never
         * deferred by the socket's limit (SO_SNDBUFFORCE: root in the guest). */
        int sndbuf = 8 * 1024 * 1024;
        if (socket(AF_INET6, SOCK_DGRAM, 0) != SEND_FD ||
            setsockopt(SEND_FD, IPPROTO_IPV6, IPV6_V6ONLY, &zero, sizeof(zero)) ||
            setsockopt(SEND_FD, IPPROTO_IP, IP_MTU_DISCOVER, &pmtudisc, sizeof(pmtudisc)) ||
            setsockopt(SEND_FD, SOL_SOCKET, SO_SNDBUFFORCE, &sndbuf, sizeof(sndbuf)) ||
            setsockopt(SEND_FD, SOL_SOCKET, SO_RCVBUFFORCE, &sndbuf, sizeof(sndbuf)) ||   /* W7 section 12 */
            setsockopt(SEND_FD, IPPROTO_IPV6, IPV6_AUTOFLOWLABEL, &zero, sizeof(zero)) ||
            setsockopt(SEND_FD, IPPROTO_IP, IP_RECVTOS, &one, sizeof(one)) ||
            setsockopt(SEND_FD, IPPROTO_IPV6, IPV6_RECVTCLASS, &one, sizeof(one)) ||
            setsockopt(SEND_FD, IPPROTO_IPV6, IPV6_RECVPKTINFO, &one, sizeof(one)) ||
            bind(SEND_FD, (struct sockaddr *)&from, sizeof(from)))
            fail(t->id, -1, "environment_failure", "sender_at_6");
        /* The generic-netlink socket replaces the last filler; no SOCK_CLOEXEC,
         * so every fixture descriptor has close-on-exec clear. */
        if (socket(AF_NETLINK, SOCK_RAW, NETLINK_GENERIC) != NETLINK_FD)
            fail(t->id, -1, "environment_failure", "genl_socket_at_7");
        /* W2 (4.1): an error acknowledgement carries only the nlmsgerr, not
         * the request (af_netlink.c:2478-2481), so a failing wg_set larger
         * than the receive buffer is acknowledged in 36 bytes. */
        int cap_ack = 1;
        if (setsockopt(NETLINK_FD, SOL_NETLINK, NETLINK_CAP_ACK, &cap_ack, sizeof(cap_ack)))
            fail(t->id, -1, "environment_failure", "netlink_cap_ack");
        if (t->net == 3) {
            /* W8: in C, the injector (the outer sender: the plain sender's
             * wildcard bind and port, so the endpoint wg0 learns from an
             * inject is unchanged) and the pin, the reference wg_netns_close
             * drops last; then back to D for good. */
            if (setns(PARK_C_FD, CLONE_NEWNET)) fail(t->id, -1, "environment_failure", "setns_c_injector");
            if (socket(AF_INET6, SOCK_DGRAM, 0) != INJECT_FD ||
                setsockopt(INJECT_FD, IPPROTO_IPV6, IPV6_V6ONLY, &zero, sizeof(zero)) ||
                setsockopt(INJECT_FD, IPPROTO_IPV6, IPV6_AUTOFLOWLABEL, &zero, sizeof(zero)) ||
                bind(INJECT_FD, (struct sockaddr *)&from, sizeof(from)))
                fail(t->id, -1, "environment_failure", "injector_at_8");
            if (open("/proc/self/ns/net", O_RDONLY) != PIN_FD) fail(t->id, -1, "environment_failure", "pin_at_9");
            if (setns(PARK_D_FD, CLONE_NEWNET)) fail(t->id, -1, "environment_failure", "setns_d_final");
            if (close(PARK_D_FD) || close(PARK_C_FD)) fail(t->id, -1, "environment_failure", "unpark_netns");
        }
        resolve_wireguard_family(t->id, NETLINK_FD);
        if (wg_exists) resolve_wg_ifindex(t->id, -1);
    }
    struct rlimit limit = {t->rlimit, t->rlimit}, actual;
    if (setrlimit(RLIMIT_NOFILE, &limit) || getrlimit(RLIMIT_NOFILE, &actual) || actual.rlim_cur != t->rlimit || actual.rlim_max != t->rlimit)
        fail(t->id, -1, "environment_failure", "rlimit_nofile");
    if (!comparisons) {
        printf("LEANUX_FIXTURE {\"id\":\"%s\",\"reserved\":[%s],\"free\":[%u,%u],\"rlimit\":[%u,%u]", t->id,
               t->net == 3 ? "0,1,2,3,4,5,6,7,8,9" : "0,1,2,3,4,5,6,7", t->net == 3 ? 10 : 8, t->rlimit - 1, t->rlimit, t->rlimit);
        /* W5: the network namespace's facts, as read back; W8: the foreign-creator
         * fixture adds the injector (8) and the pin (9) */
        if (t->net)
            printf(",\"net\":{\"auto_flowlabels\":%ld,\"icmp_ratelimit\":%ld,\"icmp6_ratelimit\":%ld,\"lo_link_local\":\"fe80::ffff:1\"}",
                   net_sysctl[0], net_sysctl[1], net_sysctl[2]);
        printf("}\n");
    }
    /* Per-task coverage stays enabled from here to exit: KCOV_DISABLE resets
     * the task's KCOV state, including the common handle this process
     * inherited for remote coverage (kcov_task_reset). Each operation resets
     * the buffer at its start and captures the count at its end; KCOV
     * appends beyond that count, so the operation's entries stay stable. */
    /* Every page of the read and write buffers is written once here, so no
     * page fault (or copy-on-write after fork) lands in a coverage window. */
    memset(read_buffer, 0xa5, sizeof(read_buffer));
    memset(write_buffer, 0, sizeof(write_buffer));
    /* SIGPIPE is blocked, not ignored (P design section 6, Q2): an EPIPE
     * write takes the full generation path and leaves SIGPIPE pending, which
     * each write observes with sigpending() outside its window. Nothing is
     * pending at the start. */
    sigset_t pipe_mask, pending;
    if (sigemptyset(&pipe_mask) || sigaddset(&pipe_mask, SIGPIPE) || sigprocmask(SIG_BLOCK, &pipe_mask, NULL))
        fail(t->id, -1, "environment_failure", "block_sigpipe");
    if (sigpending(&pending)) fail(t->id, -1, "environment_failure", "sigpending");
    for (int sig = 1; sig < NSIG; ++sig)
        if (sigismember(&pending, sig) == 1) fail(t->id, -1, "environment_failure", "signal_pending_at_start");
    if (ioctl(coverage_fd, KCOV_ENABLE, comparisons ? KCOV_TRACE_CMP : KCOV_TRACE_PC))
        fail(t->id, -1, "coverage_failure", "enable_kcov");
    for (unsigned i = 0; i < t->count; ++i) {
        const struct operation *op = &t->ops[i];
        long fd = resolve(t, op->kind, op->fd, result, i);
        long newfd = resolve(t, op->newkind, op->newfd, result, i);
        if ((op->code == OP_READ || op->code == OP_WRITE) && op->a > MAX_IO) fail(t->id, i, "invalid_input", "wire_count");
        /* A read's buffer is refilled with 0xa5; a write's is determined by
         * the trace (fill_write_buffer). */
        if (op->code == OP_READ) memset(read_buffer, 0xa5, op->a);
        if (op->code == OP_WRITE) fill_write_buffer(i, op->value, op->a);
        int pipe_fds[2] = {-1, -1};
        if (((op->code >= OP_WG_UP && op->code <= OP_WG_INJECT) || IS_LIFECYCLE_OP(op->code) || op->code == OP_WG_SET_MTU
             || op->code == OP_WG_BATCH) && !t->net)
            fail(t->id, i, "invalid_input", "wireguard_without_network_fixture");
        /* wg_up and wg_down: the flags are read before the window; without
         * a device (L) they are 0 and the SIOCSIFFLAGS reports ENODEV.
         * `was_up`: the change is a no-op (dev.c:8962). */
        struct ifreq up_request;
        int was_up = 0;
        if (op->code == OP_WG_UP || op->code == OP_WG_DOWN) {
            memset(&up_request, 0, sizeof(up_request));
            strcpy(up_request.ifr_name, "wg0");
            if (ioctl(SEND_FD, SIOCGIFFLAGS, &up_request)) {
                if (errno != ENODEV || wg_exists) fail(t->id, i, "environment_failure", "get_wg0_flags");
                memset(&up_request, 0, sizeof(up_request));
                strcpy(up_request.ifr_name, "wg0");
            } else if (!wg_exists) {
                fail(t->id, i, "environment_failure", "wg0_flags_without_wg0");
            }
            was_up = !!(up_request.ifr_flags & IFF_UP);
            if (op->code == OP_WG_UP) up_request.ifr_flags |= IFF_UP;
            else up_request.ifr_flags &= ~IFF_UP;
            /* the trace bound's origin (D3): before wg_open arms any timer,
             * and outside the coverage window (the clock read is a choice
             * record of the generic clock hook). It becomes the origin when
             * this is the trace's first up that changes the flags and it
             * succeeds (L: the bound counts from the trace's first such up)
             * [AGENT, int-dl merge]. */
            if (op->code == OP_WG_UP && !up_seen && !was_up) clock_gettime(CLOCK_BOOTTIME, &up_started);
        }
        /* A fixture pause (P design section 6): only the clock advances.
         * Before the observe wait and the advance's tick wait, so that the
         * advance still starts just after a tick (D3 merge [AGENT]). */
        if (op->pause_ms) {
            struct timespec pause = {.tv_sec = 0, .tv_nsec = (long)op->pause_ms * 1000000L};
            while (nanosleep(&pause, &pause))
                if (errno != EINTR) fail(t->id, i, "environment_failure", "pause");
        }
        /* wg_observe's wait is an idle point (D3, section 5.3): a timer that
         * fires naturally in it, and the work it queues, land in this
         * operation's remote row, so the remote area is reset before it. */
        if (op->code == OP_WG_OBSERVE) {
            if (remote) __atomic_store_n(&remote[0], 0, __ATOMIC_RELAXED);
            usleep(OBSERVE_WAIT_US);
        }
        /* wg_create and wg_delete: the temporary socket and the
         * request are prepared before the window. */
        int lifecycle_fd = -1;
        unsigned char lifecycle_body[256];
        size_t lifecycle_len = 0;
        if (op->code == OP_WG_CREATE || op->code == OP_WG_DELETE) {
            lifecycle_fd = rtnl_temporary(t, i);
            lifecycle_len = op->code == OP_WG_CREATE ? newlink_wg0(lifecycle_body, sizeof(lifecycle_body))
                                           : dellink_wg0(lifecycle_body, sizeof(lifecycle_body));
        }
        /* W9: the fixture-table operations, over the same temporary socket;
         * `a` is the family. */
        if (op->code == OP_WG_DELADDR || op->code == OP_WG_DELROUTE) {
            if (!t->net) fail(t->id, i, "invalid_input", "wireguard_without_network_fixture");
            if (op->a != 4 && op->a != 6) fail(t->id, i, "invalid_input", "fixture_family");
            lifecycle_fd = rtnl_temporary(t, i);
            lifecycle_len = op->code == OP_WG_DELADDR
                ? deladdr_wg0(op->a == 4 ? AF_INET : AF_INET6, lifecycle_body, sizeof(lifecycle_body))
                : delroute_wg0(op->a == 4 ? AF_INET : AF_INET6, lifecycle_body, sizeof(lifecycle_body));
        }
        /* E-B: the flood's socket, io_uring ring and SQEs are prepared before
         * the window (their inode/fd setup draws non-WireGuard clock records);
         * only io_uring_enter runs in the window. */
        struct flood_state flood;
        int flood_ready = 0, batch_ready = 0;
        if (op->code == OP_WG_FLOOD) {
            if (!t->net) fail(t->id, i, "invalid_input", "wireguard_without_network_fixture");
            if (flood_prep(&flood, (unsigned)op->b, (unsigned)op->a, op->payload, op->payload_len))
                fail(t->id, i, "environment_failure", "flood_prepare");
            flood_ready = 1;
        }
        /* W5: the sender's TOS / traffic class for this operation (the outer
         * DS field of an injection, the inner TOS of a transmitted packet),
         * set before the window on both levels of the dual-stack socket
         * (IP_TOS applies to a v4-mapped destination, IPV6_TCLASS otherwise;
         * a datagram socket keeps the ECN bits); and whether an injection
         * is sent from the link-local address on lo (`from: "ll"`). */
        int sender_tos = 0, sender_ll = 0;
        if (op->code == OP_WG_INJECT) {
            /* W5+W9 wire: value is tos (bits 0-7) | ll << 8 | destination << 9 (0 loopback, 1 wg0, 2 the alias) */
            if (op->value > 0x5ff || (((op->value >> 8) & 1) && op->a != 6) || (op->value >> 9) > 2)
                fail(t->id, i, "invalid_input", "wire_inject_options");
            sender_tos = (int)(op->value & 0xff);
            sender_ll = (int)((op->value >> 8) & 1);
        }
        if (op->code == OP_WG_XMIT) {
            /* W4+W5 wire: b is UDP_SEGMENT's gso_size, value is probe (bit 0) | tos << 8 */
            if (op->value > 0xff01 || (op->value & 0xfe)) fail(t->id, i, "invalid_input", "wire_xmit_options");
            sender_tos = (int)(op->value >> 8);
        }
        if (op->code == OP_WG_INJECT || op->code == OP_WG_XMIT) {
            if (setsockopt(SEND_FD, IPPROTO_IP, IP_TOS, &sender_tos, sizeof(sender_tos)) ||
                setsockopt(SEND_FD, IPPROTO_IPV6, IPV6_TCLASS, &sender_tos, sizeof(sender_tos)))
                fail(t->id, i, "environment_failure", "sender_tos");
        }
        /* W7: the batch's ring and SQEs likewise, before the window */
        if (op->code == OP_WG_BATCH) {
            int prep = batch_prep(&batch, op->payload, op->payload_len);
            if (prep) { char why[48]; snprintf(why, sizeof(why), "batch_prepare_%d_errno_%d", -prep, errno); fail(t->id, i, "invalid_input", why); }   /* 48: two ints fit (-Wformat-truncation) */
            if (batch.n != (unsigned)op->a) fail(t->id, i, "invalid_input", "batch_prepare_count");
            batch_ready = 1;
        }
        /* before the coverage window: the clock the advance's wait watches */
        struct timespec before_advance = {0};
        if (op->code == OP_WG_ADVANCE && clock_gettime(CLOCK_MONOTONIC, &before_advance))
            fail(t->id, i, "environment_failure", "advance_clock");
        /* The advance starts just after a tick: the clock is tick-granular
         * (refined-jiffies), so it changes at the tick. This fixes the
         * advance's phase: the absorbing tick comes almost 4 ms after the
         * ioctl. The record order no longer depends on it (the kernel keeps
         * interrupts off from the jump to its kind-304 record; before that
         * fix a tick in between ran the due timers before the record in about
         * 3% of the long advances' children, which jiffies_problems flags),
         * but the wait-0 control does: without the fixed phase its absorbing
         * tick also lands inside the advance's own readout or between two
         * operations (docs/2026-10-05-d3-timers.md, section 16). Bounded:
         * 20000 reads. */
        if (op->code == OP_WG_ADVANCE) {
            struct timespec now = before_advance;
            for (int spins = 0; now.tv_sec == before_advance.tv_sec && now.tv_nsec == before_advance.tv_nsec; ++spins) {
                if (spins > 20000) fail(t->id, i, "environment_failure", "advance_no_tick");
                if (clock_gettime(CLOCK_MONOTONIC, &now)) fail(t->id, i, "environment_failure", "advance_clock");
            }
            before_advance = now;
        }
        /* the lifecycle operations' wall time, taken outside the window */
        struct timespec op_started = {0}, op_finished = {0};
        if (IS_LIFECYCLE_OP(op->code) && clock_gettime(CLOCK_MONOTONIC, &op_started))
            fail(t->id, i, "environment_failure", "timing_clock");
        __atomic_store_n(&coverage[0], 0, __ATOMIC_RELAXED);
        if (remote && op->code != OP_WG_OBSERVE) __atomic_store_n(&remote[0], 0, __ATOMIC_RELAXED);
        errno = 0;
        long ret;
        switch (op->code) {
        case OP_EVENTFD2: ret = syscall(SYS_eventfd2, (unsigned long)op->a, (unsigned long)op->b); break;
        case OP_DUP: ret = syscall(SYS_dup, fd); break;
        case OP_DUP3: ret = syscall(SYS_dup3, fd, newfd, (unsigned long)op->b); break;
        case OP_CLOSE: ret = syscall(SYS_close, fd); break;
        case OP_READ: ret = syscall(SYS_read, fd, read_buffer, (unsigned long)op->a); break;
        case OP_WRITE: ret = syscall(SYS_write, fd, write_buffer, (unsigned long)op->a); break;
        case OP_FCNTL: ret = syscall(SYS_fcntl, fd, (unsigned long)op->a, (unsigned long)op->b); break;
        case OP_WG_SET: case OP_WG_GET: {
            /* WG_CMD_SET_DEVICE (acknowledged) or a WG_CMD_GET_DEVICE dump; the
             * kernel's error code becomes the operation's result. */
            if (!t->net) fail(t->id, i, "invalid_input", "wireguard_without_network_fixture");
            int error = nl_send(NETLINK_FD, wg_family,
                                op->code == OP_WG_SET ? NLM_F_REQUEST | NLM_F_ACK : NLM_F_REQUEST | NLM_F_DUMP,
                                op->code == OP_WG_SET ? WG_CMD_SET_DEVICE : WG_CMD_GET_DEVICE, op->payload, op->payload_len, 1);
            if (!error) error = nl_receive(t->id, (int)i, NETLINK_FD, GENL_HDRLEN, op->code == OP_WG_GET ? dump_hex : NULL, sizeof(dump_hex));
            if (error < 0) { errno = -error; ret = -1; } else ret = 0;
            break;
        }
        case OP_WG_UP: {
            /* dev_change_flags(wg0, flags | IFF_UP) -> wg_open. The current
             * flags were read before coverage started. */
            struct ifreq request = up_request;
            ret = syscall(SYS_ioctl, SEND_FD, SIOCSIFFLAGS, &request);
            break;
        }
        case OP_WG_XMIT: {
            /* The destination address (IPv4 as v4-mapped), then the UDP
             * payload; without one, the historic 4 bytes "leux". */
            struct sockaddr_in6 to = {.sin6_family = AF_INET6, .sin6_port = htons(SEND_PORT)};
            if (op->payload_len < sizeof(to.sin6_addr) || op->payload_len > sizeof(to.sin6_addr) + MAX_XMIT_PAYLOAD)
                fail(t->id, i, "invalid_input", "wire_address");
            memcpy(&to.sin6_addr, op->payload, sizeof(to.sin6_addr));
            /* W4: b is UDP_SEGMENT's gso_size (0: none), value 1 asks for
             * IP_PMTUDISC_PROBE for this send (restored to DO after it). */
            int probe = IP_PMTUDISC_PROBE, do_ = IP_PMTUDISC_DO;
            if ((op->value & 1) && setsockopt(SEND_FD, IPPROTO_IP, IP_MTU_DISCOVER, &probe, sizeof(probe)))
                fail(t->id, i, "environment_failure", "pmtudisc_probe");
            if (op->payload_len == sizeof(to.sin6_addr)) {
                ret = syscall(SYS_sendto, SEND_FD, "leux", 4, 0, &to, sizeof(to));
            } else if (op->b) {
                struct iovec iov = {.iov_base = (void *)(op->payload + sizeof(to.sin6_addr)),
                                    .iov_len = op->payload_len - sizeof(to.sin6_addr)};
                char control[CMSG_SPACE(sizeof(uint16_t))];
                memset(control, 0, sizeof(control));
                struct msghdr msg = {.msg_name = &to, .msg_namelen = sizeof(to), .msg_iov = &iov, .msg_iovlen = 1,
                                     .msg_control = control, .msg_controllen = sizeof(control)};
                struct cmsghdr *cm = CMSG_FIRSTHDR(&msg);
                cm->cmsg_level = SOL_UDP;
                cm->cmsg_type = UDP_SEGMENT;
                cm->cmsg_len = CMSG_LEN(sizeof(uint16_t));
                uint16_t gso = (uint16_t)op->b;
                memcpy(CMSG_DATA(cm), &gso, sizeof(gso));
                ret = syscall(SYS_sendmsg, SEND_FD, &msg, 0);
            } else {
                ret = syscall(SYS_sendto, SEND_FD, op->payload + sizeof(to.sin6_addr),
                              op->payload_len - sizeof(to.sin6_addr), 0, &to, sizeof(to));
            }
            if (op->value & 1) {
                int saved = errno;
                if (setsockopt(SEND_FD, IPPROTO_IP, IP_MTU_DISCOVER, &do_, sizeof(do_)))
                    fail(t->id, i, "environment_failure", "pmtudisc_restore");
                errno = saved;
            }
            break;
        }
        case OP_WG_SET_MTU: {
            /* W4: dev_ioctl(SIOCSIFMTU) -> dev_set_mtu(wg0, a). */
            struct ifreq request;
            memset(&request, 0, sizeof(request));
            strcpy(request.ifr_name, "wg0");
            request.ifr_mtu = (int)op->a;
            ret = syscall(SYS_ioctl, SEND_FD, SIOCSIFMTU, &request);
            break;
        }
        case OP_WG_INJECT: {
            /* A WireGuard message to wg0's port on 127.0.0.1 or ::1 (the
             * fixture's sender; IPv4 as v4-mapped). */
            struct sockaddr_in6 to = {.sin6_family = AF_INET6, .sin6_port = htons((uint16_t)op->b)};
            /* W9: the destination (the value field): 0 loopback, 1 wg0's own
             * fixture address (the local route's prefsrc becomes the source
             * wg0 learns), 2 the loopback alias 127.0.0.2 (IPv4 only; the
             * harness validates). */
            unsigned inject_dest = (unsigned)(op->value >> 9);   /* W9: the destination code */
            if (op->a == 4) {
                to.sin6_addr.s6_addr[10] = to.sin6_addr.s6_addr[11] = 0xff;
                if (inject_dest == 1) {
                    to.sin6_addr.s6_addr[12] = 10; to.sin6_addr.s6_addr[13] = 255;
                    to.sin6_addr.s6_addr[14] = 254; to.sin6_addr.s6_addr[15] = 1;
                } else {
                    to.sin6_addr.s6_addr[12] = 127;
                    to.sin6_addr.s6_addr[15] = inject_dest == 2 ? 2 : 1;
                }
            } else if (inject_dest == 1) {
                to.sin6_addr.s6_addr[0] = 0xfd; to.sin6_addr.s6_addr[2] = 0xff; to.sin6_addr.s6_addr[3] = 0xff;
                to.sin6_addr.s6_addr[15] = 1;
            } else {
                to.sin6_addr.s6_addr[15] = 1;
            }
            /* W8: in the foreign-creator fixture the outer sender is the injector in C */
            int inject_fd = t->net == 3 ? INJECT_FD : SEND_FD;
            if (sender_ll) {
                /* W5 (2.5): from fe80::1 on lo (IPV6_PKTINFO: the source and
                 * the interface), so wg0 learns the scoped endpoint
                 * [fe80::1%1]:51998 with src6 = ::1. */
                struct iovec iov = {.iov_base = (void *)op->payload, .iov_len = op->payload_len};
                union { struct cmsghdr h; unsigned char bytes[CMSG_SPACE(sizeof(struct in6_pktinfo))]; } control;
                memset(&control, 0, sizeof(control));
                struct msghdr msg = {.msg_name = &to, .msg_namelen = sizeof(to), .msg_iov = &iov, .msg_iovlen = 1,
                                     .msg_control = &control, .msg_controllen = sizeof(control)};
                struct cmsghdr *c = CMSG_FIRSTHDR(&msg);
                c->cmsg_level = IPPROTO_IPV6;
                c->cmsg_type = IPV6_PKTINFO;
                c->cmsg_len = CMSG_LEN(sizeof(struct in6_pktinfo));
                struct in6_pktinfo pi;
                memset(&pi, 0, sizeof(pi));
                memcpy(&pi.ipi6_addr, LO_LINK_LOCAL, 16);
                pi.ipi6_ifindex = 1;
                memcpy(CMSG_DATA(c), &pi, sizeof(pi));
                ret = syscall(SYS_sendmsg, inject_fd, &msg, 0);
            } else {
                ret = syscall(SYS_sendto, inject_fd, op->payload, op->payload_len, 0, &to, sizeof(to));
            }
            break;
        }
        case OP_WG_NETNS_CLOSE: {
            /* W8 (section 3.2): C's holders go, the injector and the listeners
             * first (their put_net is RCU-deferred), then after NETNS_SETTLE_US
             * the pin, the last reference: cleanup_net is queued inside this
             * close, so its kind-307 record lands in this operation's task
             * stream, and the teardown's section runs in the wait below. */
            if (t->net != 3) fail(t->id, i, "invalid_input", "netns_close_outside_foreign_creator");
            if (netns_closed) fail(t->id, i, "invalid_input", "netns_close_twice");
            ret = syscall(SYS_close, INJECT_FD);
            if (ret == 0) ret = syscall(SYS_close, LISTEN6_FD);
            if (ret == 0) ret = syscall(SYS_close, LISTEN4_FD);
            if (ret == 0) {
                settle_spin(t->id, i, NETNS_SETTLE_US);   /* the RCU grace period passes at the ticks */
                ret = syscall(SYS_close, PIN_FD);
            }
            if (ret != 0) fail(t->id, i, "environment_failure", "netns_close");
            netns_closed = 1;
            break;
        }
        case OP_WG_ADVANCE: {
            /* D3: the virtual time advance, on this process's KCOV
             * descriptor (fd 3); the kernel records {jiffies before, after}
             * (kind 304) in the task stream. */
            unsigned long ticks = op->a;
            ret = syscall(SYS_ioctl, 3, KCOV_LEANUX_TIME_ADVANCE, &ticks);
            break;
        }
        case OP_PIPE2: ret = syscall(SYS_pipe2, pipe_fds, (unsigned long)op->b); break;
        case OP_WG_FLOOD: {
            /* E-B: submit the prepared io_uring flood batch (op->a count, op->b
             * port); op->payload is an optional bundled valid initiation (the
             * merged-injection negative control). */
            ret = flood_enter(&flood);
            break;
        }
        case OP_WG_BATCH: {
            /* W7: submit the prepared batch (op->a items); the completions
             * present at the return are reported as the operation's cqes. */
            ret = batch_enter(&batch);
            break;
        }
        case OP_WG_CREATE: case OP_WG_DELETE: {
            /* L: RTM_NEWLINK (wg_newlink, register_netdevice) or RTM_DELLINK
             * (unregister, netdev_run_todo, wg_destruct), both complete
             * inside send(); recv() reads the acknowledgement, whose error
             * code is the result. */
            int error = nl_send(lifecycle_fd, op->code == OP_WG_CREATE ? RTM_NEWLINK : RTM_DELLINK,
                                op->code == OP_WG_CREATE ? NEWLINK_FLAGS : NLM_F_REQUEST | NLM_F_ACK, 0, lifecycle_body,
                                lifecycle_len, 0);
            if (!error) error = nl_receive(t->id, (int)i, lifecycle_fd, 0, NULL, 0);
            if (error < 0) { errno = -error; ret = -1; } else ret = 0;
            break;
        }
        case OP_WG_DELADDR: case OP_WG_DELROUTE: {
            /* W9: RTM_DELADDR of wg0's fixture address or RTM_DELROUTE of
             * the default route via wg0; the acknowledgement's error code is
             * the result (EADDRNOTAVAIL, ESRCH when absent). */
            int error = nl_send(lifecycle_fd, op->code == OP_WG_DELADDR ? RTM_DELADDR : RTM_DELROUTE,
                                NLM_F_REQUEST | NLM_F_ACK, 0, lifecycle_body, lifecycle_len, 0);
            if (!error) error = nl_receive(t->id, (int)i, lifecycle_fd, 0, NULL, 0);
            if (error < 0) { errno = -error; ret = -1; } else ret = 0;
            if (op->code == OP_WG_DELADDR && op->a == 4 && ret == 0) addr4_deleted = 1;
            break;
        }
        case OP_WG_DOWN: {
            /* L: dev_change_flags(wg0, flags & ~IFF_UP) -> wg_stop. */
            struct ifreq request = up_request;
            ret = syscall(SYS_ioctl, SEND_FD, SIOCSIFFLAGS, &request);
            break;
        }
        case OP_WG_OBSERVE:
            /* The first datagram at the IPv4 listener, if any (recvmsg, for
             * its TOS cmsg: W5); the rest are drained after coverage stops. */
            ret = recv_with_cmsg(LISTEN4_FD, MSG_DONTWAIT, NULL, NULL, &first_tos, NULL);
            break;
        default: fail(t->id, i, "invalid_input", "wire_opcode");
        }
        int captured_errno = errno;
        unsigned long count = __atomic_load_n(&coverage[0], __ATOMIC_RELAXED);
        /* close the flood's socket and ring after the task count is captured
         * (the packets are already queued in wg0; the worker drains them in the
         * post-op wait regardless) so the fd teardown is outside the window. */
        if (flood_ready) flood_cleanup(&flood);
        /* W7: the batch's completions, reported outside the window (a console
         * write inside it would add the tty's path to the coverage) */
        if (batch_ready) {
            if (!comparisons) {
                printf("LEANUX_WGBATCH {\"id\":\"%s\",\"index\":%u,\"cqes\":[", t->id, i);
                for (unsigned j = 0; j < batch.n; ++j) {
                    if (batch.present[j]) printf("%s%ld", j ? "," : "", batch.res[j]);
                    else printf("%snull", j ? "," : "");
                }
                printf("]}\n");
            }
            batch_cleanup(&batch);
        }
        if (IS_LIFECYCLE_OP(op->code)) {
            if (clock_gettime(CLOCK_MONOTONIC, &op_finished)) fail(t->id, i, "environment_failure", "timing_clock");
            printf("LEANUX_TIMING {\"id\":\"%s\",\"index\":%u,\"mode\":\"%s\",\"op\":%u,\"ns\":%lld}\n", t->id, i,
                   comparisons ? "cmp" : "pc", op->code,
                   (op_finished.tv_sec - op_started.tv_sec) * 1000000000LL + (op_finished.tv_nsec - op_started.tv_nsec));
        }
        if (lifecycle_fd >= 0 && close(lifecycle_fd)) fail(t->id, i, "environment_failure", "lifecycle_rtnetlink_close");
        /* L: what the fixture knows about wg0 after the operation. */
        if (op->code == OP_WG_CREATE && ret == 0) {
            if (wg_exists) fail(t->id, i, "environment_failure", "wg_create_succeeded_twice");
            wg_exists = 1;
            first_up = 1;
            resolve_wg_ifindex(t->id, (int)i);
        }
        if (op->code == OP_WG_DELETE && ret == 0) {
            if (!wg_exists) fail(t->id, i, "environment_failure", "wg_delete_without_wg0");
            wg_exists = 0;
            first_up = 1;
        }
        /* Outside the window: SIGPIPE pending after a write; any other
         * pending signal is outside the fixture. */
        if (sigpending(&pending)) fail(t->id, i, "environment_failure", "sigpending");
        for (int sig = 1; sig < NSIG; ++sig)
            if (sig != SIGPIPE && sigismember(&pending, sig) == 1)
                fail(t->id, i, "environment_failure", "unexpected_pending_signal");
        result[i].sigpipe = sigismember(&pending, SIGPIPE) == 1;
        /* Outside the coverage window: the dump's attribute payloads. */
        if (op->code == OP_WG_GET && !comparisons && ret == 0)
            printf("LEANUX_WG {\"id\":\"%s\",\"index\":%u,\"payloads\":[%s]}\n", t->id, i, dump_hex);
        /* A successful up that changed the flags gets wg0's addresses and
         * routes (the first since creation, or again after a down); the
         * rekey bound counts from the trace's first such up, timed before
         * its window. */
        int waited = 0;
        if (op->code == OP_WG_UP && ret == 0 && !was_up) {
            if (!up_seen) {
                went_up = up_started;
                up_seen = 1;
            }
            /* W9 (docs/2026-10-06-w8-w9-netns-routing.md 14.3b): the
             * operation's wait comes BEFORE the route adds, so the handshake
             * worker queued inside the ioctl (wg_open's keepalives) always
             * sends before them: each add is a rt_cache_flush, and a dst
             * cached by that send either survives it or not depending on
             * which ran first, an order nothing records. The fixture makes
             * it one order. No added time: this is the wait below, moved. */
            usleep(QUEUE_WAIT_US);
            waited = 1;
            route_into_wg0(t->id, i, first_up);
            first_up = 0;
        }
        if (op->code == OP_WG_OBSERVE) observe(t, i, ret, comparisons);
        /* The handshake worker runs after the send returns. An operation
         * that can queue the handshake send worker (wg_set, wg_up, wg_xmit)
         * waits for it too, so the worker's remote section lands in it. */
        if (op->code == OP_WG_INJECT) usleep(OBSERVE_WAIT_US);
        if ((op->code == OP_WG_SET || op->code == OP_WG_UP || op->code == OP_WG_XMIT) && !waited) usleep(QUEUE_WAIT_US);
        /* E-B: wait for the receive worker to drain the flood (its discarded
         * section) in this operation's window (~1 ms drain, measured). Keep the
         * wait short: the following injection must reach the worker within the
         * one-second last_under_load decay (§4.1). */
        if (op->code == OP_WG_FLOOD) usleep(QUEUE_WAIT_US);
        /* W7: the batch's wait (op->b ms, the trace's wait_ms), in which the
         * kworkers run what it queued; a worker outliving it shows as missing
         * section records */
        if (op->code == OP_WG_BATCH) usleep((useconds_t)op->b * 1000);
        /* W8: the netns teardown (cleanup_net's section) runs in this wait */
        if (op->code == OP_WG_NETNS_CLOSE) usleep(NETNS_WAIT_US);
        if (op->code == OP_WG_ADVANCE) {
            /* An advance that fails is not a trace operation the mirror can
             * follow: fail the trace. Then wait for the tick that absorbs the
             * jump (bounded: 1 s of real time), then ADVANCE_WAIT_US. */
            if (ret != 0) fail(t->id, i, "environment_failure", "time_advance");
            long long jump = (long long)op->a * TICK_NS;
            int polls = 0;
            for (; ADVANCE_ABSORB;) {
                struct timespec now;
                if (clock_gettime(CLOCK_MONOTONIC, &now)) fail(t->id, i, "environment_failure", "advance_clock");
                if ((now.tv_sec - before_advance.tv_sec) * 1000000000LL + (now.tv_nsec - before_advance.tv_nsec) >= jump)
                    break;
                if (++polls > 1000) fail(t->id, i, "environment_failure", "advance_not_absorbed");
                usleep(1000);
            }
            if (ADVANCE_WAIT_US) usleep(ADVANCE_WAIT_US);
            advanced_ns += jump;
        }
        if (up_seen) {
            struct timespec now;
            clock_gettime(CLOCK_BOOTTIME, &now);
            since_up_ns = (now.tv_sec - went_up.tv_sec) * 1000000000LL + (now.tv_nsec - went_up.tv_nsec) - advanced_ns;
            if (since_up_ns > REKEY_BOUND_NS)
                fail(t->id, i, "environment_failure", "trace_exceeds_rekey_bound");
        }
        /* KCOV stops counting once the buffer is full, so "full" is the last
         * value it can reach: CAPACITY - 1 PCs, or (CAPACITY - 1) / 4 records. */
        if (!count || count >= (comparisons ? (CAPACITY - 1) / 4 : CAPACITY - 1))
            fail(t->id, i, "coverage_failure", "empty_or_full_kcov");
        result[i].error = ret == -1 ? captured_errno : 0;
        result[i].ret = ret == -1 ? -captured_errno : ret;
        if ((op->code == OP_READ || op->code == OP_WRITE) && ret > (long)op->a)
            fail(t->id, i, "environment_failure", "io_return_exceeds_count");
        if (op->code == OP_READ && ret > 0) {
            memcpy(result[i].bytes, read_buffer, (size_t)(ret < READ_HEAD ? ret : READ_HEAD));
            blake2s256(read_buffer, (size_t)ret, result[i].digest);
        }
        if (op->code == OP_PIPE2) {
            if (ret == 0 && (pipe_fds[0] < 0 || pipe_fds[1] < 0 || pipe_fds[0] == pipe_fds[1]))
                fail(t->id, i, "environment_failure", "pipe2_descriptors");
            result[i].fds[0] = ret == 0 ? pipe_fds[0] : -1;
            result[i].fds[1] = ret == 0 ? pipe_fds[1] : -1;
        }
        /* The remote stream: the dispatch sections (the NET_RX vector and
         * the work items in the dispatch set) that stopped during this
         * operation, collected under this process's common handle. The
         * operations that queue work waited for it. */
        unsigned long remote_count = 0;
        if (remote) {
            remote_count = __atomic_load_n(&remote[0], __ATOMIC_RELAXED);
            if (remote_count >= (comparisons ? (CAPACITY - 1) / 4 : CAPACITY - 1))
                fail(t->id, i, "coverage_failure", "full_remote_kcov");
        }
        /* every trace: the generic clock hooks also fire on file paths */
        {
            count = split_hidden("LEANUX_HIDDEN", t, i, coverage, count, comparisons);
            if (remote) remote_count = split_hidden("LEANUX_RHIDDEN", t, i, remote, remote_count, comparisons);
        }
        if (comparisons) {
            /* The remote stream's comparisons: the handshake worker's peer
             * reference counts (stage C) are declared comparisons. */
            print_records("LEANUX_CMP", t->id, i, coverage, count, NULL);
            if (remote) print_records("LEANUX_RCMP", t->id, i, remote, remote_count, cmp_block);
            continue;
        }
        print_pcs("LEANUX_COVERAGE", t->id, i, coverage, count);
        if (remote) print_pcs("LEANUX_RCOVERAGE", t->id, i, remote, remote_count);
    }
    if (up_seen)
        printf("LEANUX_TIMING {\"id\":\"%s\",\"mode\":\"%s\",\"since_up_ns\":%lld}\n", t->id,
               comparisons ? "cmp" : "pc", since_up_ns);
    if (comparisons) {
        /* Per operation: ret, bytes, and the fds/digest/sigpipe fields
         * (null where an operation has none), for the determinism check. */
        printf("LEANUX_CMP_RESULT {\"id\":\"%s\",\"rets\":[", t->id);
        for (unsigned i = 0; i < t->count; ++i) printf("%s%ld", i ? "," : "", result[i].ret);
        printf("],\"bytes\":[");
        for (unsigned i = 0; i < t->count; ++i) { printf("%s", i ? "," : ""); print_head(&t->ops[i], &result[i]); }
        printf("],\"fds\":[");
        for (unsigned i = 0; i < t->count; ++i) { printf("%s", i ? "," : ""); print_fds(&t->ops[i], &result[i]); }
        printf("],\"digest\":[");
        for (unsigned i = 0; i < t->count; ++i) { printf("%s", i ? "," : ""); print_digest(&t->ops[i], &result[i]); }
        printf("],\"sigpipe\":[");
        for (unsigned i = 0; i < t->count; ++i)
            if (t->ops[i].code == OP_WRITE) printf("%s%d", i ? "," : "", result[i].sigpipe); else printf("%snull", i ? "," : "");
        printf("]}\n");
        fflush(stdout);
        task_steering_status(t, coverage_fd, comparisons);
        alloc_status(t, coverage_fd, comparisons);
        /* W2 (4.2, C1): the netlink sockets close before wg0 is deleted, so
         * a dump still running on one of them (netlink_release runs its
         * `done`, dropping the device reference) can never hold RTM_DELLINK
         * in netdev_wait_allrefs_any. Outside every window. */
        if (t->net && close(NETLINK_FD)) fail(t->id, -1, "environment_failure", "close_netlink");
        if (t->net) delete_wg0(t->id);
        fflush(stdout);   /* a bulk trace's buffered rows */
        _exit(0);
    }
    task_steering_status(t, coverage_fd, comparisons);
    alloc_status(t, coverage_fd, comparisons);
    printf("LEANUX_RESULT {\"version\":1,\"id\":\"%s\",\"observations\":[", t->id);
    for (unsigned i = 0; i < t->count; ++i) {
        printf("%s{\"index\":%u,\"ret\":%ld,\"errno\":", i ? "," : "", i, result[i].ret);
        if (result[i].error) printf("%d", result[i].error); else printf("null");
        printf(",\"bytes\":");
        print_head(&t->ops[i], &result[i]);
        if (t->ops[i].code == OP_READ) { printf(",\"digest\":"); print_digest(&t->ops[i], &result[i]); }
        if (t->ops[i].code == OP_WRITE) printf(",\"sigpipe\":%d", result[i].sigpipe);
        if (t->ops[i].code == OP_PIPE2) { printf(",\"fds\":"); print_fds(&t->ops[i], &result[i]); }
        printf("}");
    }
    printf("],\"branches\":[]}\n");
    fflush(stdout);
    if (t->net && close(NETLINK_FD)) fail(t->id, -1, "environment_failure", "close_netlink");   /* W2 4.2 (C1) */
    if (t->net) delete_wg0(t->id);
    fflush(stdout);   /* a bulk trace's buffered rows */
    _exit(0);
}

/* D3: the timekeeper's clocksource at batch start and end (the harness fails
 * a batch unless both are EXPECTED_CLOCKSOURCE; docs/2026-10-05-d3-timers.md,
 * section 4.3). */
static void clocksource_row(const char *at)
{
    char names[2][256];
    const char *files[2] = {"/sys/devices/system/clocksource/clocksource0/current_clocksource",
                            "/sys/devices/system/clocksource/clocksource0/available_clocksource"};
    for (int k = 0; k < 2; ++k) {
        FILE *f = fopen(files[k], "r");
        if (!f || !fgets(names[k], sizeof(names[k]), f)) fail("batch", -1, "environment_failure", "read_clocksource");
        fclose(f);
        names[k][strcspn(names[k], "\n")] = 0;
        for (char *c = names[k]; *c; ++c)
            if (*c == '"' || *c == '\\' || (unsigned char)*c < 0x20) fail("batch", -1, "environment_failure", "clocksource_name");
    }
    /* available_clocksource ends with a space */
    size_t len = strlen(names[1]);
    while (len && names[1][len - 1] == ' ') names[1][--len] = 0;
    printf("LEANUX_CLOCKSOURCE {\"at\":\"%s\",\"current\":\"%s\",\"available\":\"%s\"}\n", at, names[0], names[1]);
    fflush(stdout);
}

/* The parent's watchdog (P design section 6): SIGALRM kills the running
 * child's process group; the child's own signal state is untouched. A killed
 * child is a LEANUX_CHILD_FAILURE, which fails the chunk. */
static volatile pid_t watched;
static volatile sig_atomic_t watchdog_fired;

static void on_watchdog(int sig)
{
    (void)sig;
    if (watched > 0) {
        kill(-watched, SIGKILL);
        kill(watched, SIGKILL);
        watchdog_fired = 1;
    }
}

int main(int argc, char **argv)
{
    setvbuf(stdout, NULL, _IOLBF, 0);
    blake2s_self_test();
    struct sigaction watchdog = {.sa_handler = on_watchdog, .sa_flags = SA_RESTART};
    if (sigemptyset(&watchdog.sa_mask) || sigaction(SIGALRM, &watchdog, NULL))
        fail("batch", -1, "environment_failure", "watchdog_handler");
    if (argc != 2) fail("batch", -1, "invalid_input", "wire_argument");
    FILE *input = fopen(argv[1], "r");
    if (!input) fail("batch", -1, "environment_failure", "open_wire");
    unsigned total;
    if (!fgets(line, sizeof(line), input) || strcmp(line, "LEANUX_WIRE_V2\n") ||
        !fgets(line, sizeof(line), input) || sscanf(line, "%u", &total) != 1 || total < 1 || total > 4096)
        fail("batch", -1, "invalid_input", "wire_header");
    struct utsname identity;
    if (uname(&identity)) fail("batch", -1, "environment_failure", "uname");
    /* W8: the pin holder and its socket pairs, before any trace (section 3.2) */
    if (socketpair(AF_UNIX, SOCK_STREAM, 0, pin_sock) || socketpair(AF_UNIX, SOCK_STREAM, 0, pin_sock + 2))
        fail("batch", -1, "environment_failure", "pin_sock");
    pid_t holder = fork();
    if (holder < 0) fail("batch", -1, "environment_failure", "fork_pin_holder");
    if (!holder) pin_holder();
    /* Block until the kernel's RNG is initialized. WireGuard's handshake
     * worker calls wait_for_random_bytes(), and its receive path drops
     * handshakes until rng_is_initialized(): neither may depend on how long
     * the guest has been up. */
    unsigned char seed;
    if (syscall(SYS_getrandom, &seed, 1, 0) != 1) fail("batch", -1, "environment_failure", "getrandom");
    printf("LEANUX_KERNEL %s\n", identity.release);
    clocksource_row("start");
    /* D n addr...: the dispatch set, in hex */
    int consumed = 0;
    if (!fgets(line, sizeof(line), input) || sscanf(line, "D %u%n", &dispatch.n, &consumed) != 1 || dispatch.n > DISPATCH_MAX)
        fail("batch", -1, "invalid_input", "wire_dispatch");
    for (unsigned k = 0; k < dispatch.n; ++k) {
        int more = 0;
        if (sscanf(line + consumed, " %" SCNx64 "%n", &dispatch.funcs[k], &more) != 1 || !dispatch.funcs[k])
            fail("batch", -1, "invalid_input", "wire_dispatch");
        consumed += more;
    }
    if (strcmp(line + consumed, "\n")) fail("batch", -1, "invalid_input", "wire_dispatch");
    /* A 0|1: the arm records (D3) */
    unsigned arm = 2;
    if (!fgets(line, sizeof(line), input) || sscanf(line, "A %u%n", &arm, &consumed) != 1 || arm > 1 ||
        strcmp(line + consumed, "\n"))
        fail("batch", -1, "invalid_input", "wire_arm_records");
    dispatch.flags = arm ? DISPATCH_ARM_RECORDS : 0;
    /* M flags n lo hi ...: the allocation set (A), in hex */
    if (!fgets(line, sizeof(line), input) || sscanf(line, "M %u %u%n", &alloc.flags, &alloc.n, &consumed) != 2 ||
        alloc.n > ALLOC_RANGES_MAX || alloc.flags > 15)   /* bits 1-3: control kernel only */
        fail("batch", -1, "invalid_input", "wire_allocation_set");
    for (unsigned k = 0; k < alloc.n; ++k) {
        int more = 0;
        if (sscanf(line + consumed, " %" SCNx64 " %" SCNx64 "%n", &alloc.r[k].lo, &alloc.r[k].hi, &more) != 2 ||
            alloc.r[k].lo >= alloc.r[k].hi || (k && alloc.r[k - 1].hi > alloc.r[k].lo))
            fail("batch", -1, "invalid_input", "wire_allocation_set");
        consumed += more;
    }
    if (strcmp(line + consumed, "\n")) fail("batch", -1, "invalid_input", "wire_allocation_set");
    if (alloc.n || alloc.flags) {
        /* the TSC rate, to convert the unwind cycles (A0) */
        FILE *cpuinfo = fopen("/proc/cpuinfo", "r");
        char mhz[64] = "";
        while (cpuinfo && fgets(line, sizeof(line), cpuinfo))
            if (!strncmp(line, "cpu MHz", 7) && sscanf(line, "cpu MHz : %63s", mhz) == 1) break;
        if (cpuinfo) fclose(cpuinfo);
        if (!mhz[0] || strspn(mhz, "0123456789.") != strlen(mhz)) fail("batch", -1, "environment_failure", "cpu_mhz");
        printf("LEANUX_ALLOC_TSC {\"mhz\":\"%s\"}\n", mhz);
    }
    unsigned failures = 0;
    for (unsigned t = 0; t < total; ++t) {
        static struct trace trace;
        if (!fgets(line, sizeof(line), input) ||
            sscanf(line, "T %80s %u %u %u %u %x %u", trace.id, &trace.count, &trace.rlimit, &trace.net, &trace.nsteer,
                   &trace.arm, &trace.nroutes) != 7 ||
            trace.count < 1 || trace.count > MAX_OPS || trace.rlimit < 8 || trace.rlimit > 1024 || trace.net > 3 ||
            trace.nsteer > STEER_MAX || (trace.arm >> dispatch.n) || (trace.net == 3 && trace.rlimit < 10) ||
            trace.nroutes > MAX_FIXTURE_ROUTES || (trace.nroutes && trace.net != 1))
            fail("batch", -1, "invalid_input", "wire_trace");
        /* W8: the subset of the dispatch set this trace arms (section 3.2):
         * a foreign-creator trace arms cleanup_net; a plain one never sees a
         * stale teardown's section because it does not arm it. */
        memset(&trace_dispatch, 0, sizeof(trace_dispatch));
        trace_dispatch.flags = dispatch.flags;
        for (unsigned k = 0; k < dispatch.n; ++k)
            if (trace.arm & (1u << k)) trace_dispatch.funcs[trace_dispatch.n++] = dispatch.funcs[k];
        /* W4: the fixture's routes into wg0 (family, destination, MTU). */
        for (unsigned k = 0; k < trace.nroutes; ++k) {
            struct fixture_route *r = &trace.routes[k];
            char hex[40];
            if (!fgets(line, sizeof(line), input) || sscanf(line, "R %u %39s %u", &r->family, hex, &r->mtu) != 3 ||
                (r->family != 4 && r->family != 6) || strlen(hex) != (r->family == 4 ? 8u : 32u) ||
                r->mtu < 68 || r->mtu > 65535)
                fail("batch", -1, "invalid_input", "wire_route");
            for (size_t b = 0; b < strlen(hex) / 2; ++b) {
                unsigned byte;
                if (sscanf(hex + 2 * b, "%2x", &byte) != 1) fail("batch", -1, "invalid_input", "wire_route");
                r->dst[b] = (unsigned char)byte;
            }
        }
        for (unsigned i = 0; i < trace.count; ++i) {
            struct operation *op = &trace.ops[i];
            int consumed = 0;
            /* opcode, fd kind and value, newfd kind and value, a, b, value,
             * pause_ms (the ninth field, P design section 6) */
            if (!fgets(line, sizeof(line), input) || sscanf(line, "%u %u %lld %u %lld %u %u %" SCNu64 " %u%n",
                &op->code, &op->kind, &op->fd, &op->newkind, &op->newfd, &op->a, &op->b, &op->value, &op->pause_ms,
                &consumed) != 9 || op->pause_ms > PAUSE_MS_MAX || op->kind > 3 || op->newkind > 3)
                fail(trace.id, i, "invalid_input", "wire_operation");
            op->payload_len = 0;
            if (op->code == OP_WG_SET || op->code == OP_WG_GET || op->code == OP_WG_XMIT || op->code == OP_WG_INJECT || op->code == OP_WG_FLOOD
                || op->code == OP_WG_BATCH) {
                /* A WireGuard operation carries its attribute payload as hex. */
                const char *hex = line + consumed;
                if (*hex++ != ' ') fail(trace.id, i, "invalid_input", "wire_payload");
                while (hex[0] && hex[0] != '\n') {
                    unsigned byte;
                    if (op->payload_len >= MAX_PAYLOAD || sscanf(hex, "%2x", &byte) != 1 || !hex[1])
                        fail(trace.id, i, "invalid_input", "wire_payload");
                    op->payload[op->payload_len++] = (unsigned char)byte;
                    hex += 2;
                }
            }
        }
        for (unsigned k = 0; k < trace.nsteer; ++k) {
            struct steer_entry *e = &trace.steer[k];
            int consumed = 0;
            memset(e, 0, sizeof(*e));
            if (!fgets(line, sizeof(line), input) ||
                sscanf(line, "S %u %u %u %u %" SCNx64 " %" SCNx64 " %" SCNx64 " %" SCNx64 "%n", &e->kind, &e->len,
                       &e->draw, &e->flags, &e->ips[0], &e->ips[1], &e->ips[2], &e->ips[3], &consumed) != 8 ||
                e->len > sizeof(e->value) || e->draw > 1 || e->flags > STEER_CHAIN)
                fail(trace.id, -1, "invalid_input", "wire_steering");
            const char *hex = line + consumed;
            if (*hex == ' ') ++hex;
            for (unsigned b = 0; b < (e->draw ? 0 : e->len); ++b) {
                unsigned byte;
                if (sscanf(hex + 2 * b, "%2x", &byte) != 1) fail(trace.id, -1, "invalid_input", "wire_steering");
                e->value[b] = (unsigned char)byte;
            }
        }
        for (int comparisons = 0; comparisons < 2; ++comparisons) {
            pid_t child = fork();
            if (child < 0) fail(trace.id, -1, "environment_failure", "fork");
            if (!child) execute(&trace, fileno(input), comparisons);
            int status;
            unsigned pauses = 0;
            unsigned long long advanced_ns = 0;
            for (unsigned i = 0; i < trace.count; ++i) {
                pauses += trace.ops[i].pause_ms;
                if (trace.ops[i].code == OP_WG_ADVANCE) advanced_ns += trace.ops[i].a * (unsigned long long)TICK_NS;
            }
            /* alarm() runs on the monotonic clock, which under refined-jiffies
             * jumps with every wg_advance (D3): the advanced time is added, or
             * a long advance fires the watchdog at once (the first run after
             * the merge with P lost 125 traces to it) [AGENT]. */
            unsigned long long seconds = WATCHDOG_BASE_SECONDS + WATCHDOG_OP_SECONDS * trace.count + (pauses + 999) / 1000
                                         + (advanced_ns + 999999999ULL) / 1000000000ULL;
            if (seconds > UINT_MAX) fail(trace.id, -1, "invalid_input", "watchdog_seconds");
            watchdog_fired = 0;
            watched = child;
            alarm((unsigned)seconds);
            pid_t waited = waitpid(child, &status, 0);
            watched = 0;
            alarm(0);
            if (waited != child) fail(trace.id, -1, "environment_failure", "wait_child");
            if (!WIFEXITED(status) || WEXITSTATUS(status)) {
                printf("LEANUX_CHILD_FAILURE {\"id\":\"%s\",\"status\":%d,\"watchdog\":%d}\n", trace.id, status,
                       (int)watchdog_fired);
                ++failures;
            }
        }
    }
    if (fgetc(input) != EOF) fail("batch", -1, "invalid_input", "wire_trailing_data");
    fclose(input);
    clocksource_row("end");
    printf("LEANUX_BATCH_DONE traces=%u failures=%u\n", total, failures);
    return failures ? 1 : 0;
}
