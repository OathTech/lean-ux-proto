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

#define MAX_OPS 64
/* The KCOV area in words, task and remote alike (L, docs/2026-10-05-l-lifecycle.md
 * section 10: a wg_create window's comparison child exceeds 64 K words; E-B: an
 * io_uring flood crossing 512 runs ~600 UDP sends inline in the trace task with
 * KCOV on, so both streams need headroom). The host's bounds follow it
 * (harness/trace.py KCOV_CAPACITY). */
#define CAPACITY (1024UL * 1024)
#define MAX_PAYLOAD 32768
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
/* A wg_xmit payload: at most wg0's MTU (1420) less the IPv4 and UDP headers. */
#define MAX_XMIT_PAYLOAD 1392
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
/* 20-24 are reserved for the W streams (harness/trace.py RESERVED_OPCODES,
 * docs/2026-10-11-interface.md): 20 wg_get_start and 21 wg_get_recv (W2),
 * 22 wg_netns_close (W8), 23 wg_deladdr and 24 wg_delroute (W9). No define
 * until a stream lands: the opcode switch's default fails any such code. */
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
     * network fixture without wg0 (L, "net_fixture": "bare") */
    char id[81]; unsigned count; unsigned rlimit; unsigned net; struct operation ops[MAX_OPS];
    unsigned nsteer; struct steer_entry steer[STEER_MAX];
};
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

struct occurrence { unsigned long pc; unsigned long position; };
static struct occurrence order[CAPACITY];
static unsigned char first[CAPACITY];

struct record_occurrence { unsigned long record[4]; unsigned long position; };
static struct record_occurrence records[CAPACITY / 4];

static int compare_record(const void *a, const void *b)
{
    const struct record_occurrence *x = a, *y = b;
    int order = memcmp(x->record, y->record, sizeof(x->record));
    if (order) return order;
    return x->position < y->position ? -1 : x->position > y->position;
}

static int compare_occurrence(const void *a, const void *b)
{
    const struct occurrence *x = a, *y = b;
    if (x->pc != y->pc) return x->pc < y->pc ? -1 : 1;
    return x->position < y->position ? -1 : x->position > y->position;
}

/* ---- Netlink (network fixture traces only) ---------------------------- */
static unsigned char nl_buffer[1 << 16];
static unsigned short wg_family;

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
static int nl_receive(int fd, size_t skip, char *out, size_t out_size)
{
    size_t used = 0;
    if (out) { out[0] = 0; }
    int first = 1;
    for (;;) {
        ssize_t n = recv(fd, nl_buffer, sizeof(nl_buffer), 0);
        if (n < 0) return -errno;
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

/* Fresh network namespace with `lo` up and, unless the trace asks for the
 * bare fixture, a down `wg0`, created over a temporary rtnetlink socket that
 * is closed again before the fixture descriptors are opened, so the
 * descriptor-table history matches the plain fixture. */
static void network_fixture(const char *id, int bare)
{
    if (unshare(CLONE_NEWNET)) fail(id, -1, "environment_failure", "unshare_net");
    net_live = 1;
    int rtnl = socket(AF_NETLINK, SOCK_RAW | SOCK_CLOEXEC, NETLINK_ROUTE);
    if (rtnl < 0) fail(id, -1, "environment_failure", "rtnetlink_socket");
    unsigned char payload[256];
    if (!bare) {
        size_t len = newlink_wg0(payload, sizeof(payload));
        if (nl_send(rtnl, RTM_NEWLINK, NEWLINK_FLAGS, 0, payload, len, 0) || nl_receive(rtnl, 0, NULL, 0))
            fail(id, -1, "environment_failure", "create_wg0");
        wg_exists = 1;
        first_up = 1;
    }
    /* lo up: what wg0 sends to 127.0.0.1 and ::1 reaches the listeners. */
    struct ifinfomsg up = {.ifi_family = AF_UNSPEC, .ifi_index = 1, .ifi_flags = IFF_UP, .ifi_change = IFF_UP};
    if (nl_send(rtnl, RTM_NEWLINK, NLM_F_REQUEST | NLM_F_ACK, 0, (unsigned char *)&up, sizeof(up), 0) ||
        nl_receive(rtnl, 0, NULL, 0))
        fail(id, -1, "environment_failure", "lo_up");
    if (close(rtnl)) fail(id, -1, "environment_failure", "close_rtnetlink");
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
    if (nl_send(rtnl, RTM_DELLINK, NLM_F_REQUEST | NLM_F_ACK, 0, payload, len, 0) || nl_receive(rtnl, 0, NULL, 0))
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
    if (!nl_send(rtnl, RTM_DELLINK, NLM_F_REQUEST | NLM_F_ACK, 0, payload, len, 0)) (void)nl_receive(rtnl, 0, NULL, 0);
    close(rtnl);
}

static void resolve_wireguard_family(const char *id, int fd)
{
    unsigned char payload[64];
    size_t len = 0;
    attr(payload, &len, CTRL_ATTR_FAMILY_NAME, WG_GENL_NAME, sizeof(WG_GENL_NAME));
    if (nl_send(fd, GENL_ID_CTRL, NLM_F_REQUEST, CTRL_CMD_GETFAMILY, payload, len, 2))
        fail(id, -1, "environment_failure", "genl_getfamily");
    ssize_t n = recv(fd, nl_buffer, sizeof(nl_buffer), 0);
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
static void print_records(const char *tag, const char *id, unsigned i, const unsigned long *area, unsigned long count)
{
    for (unsigned long k = 0; k < count; ++k) {
        memcpy(records[k].record, area + 1 + 4 * k, sizeof(records[k].record));
        records[k].position = k;
    }
    qsort(records, count, sizeof(*records), compare_record);
    memset(first, 0, count);
    for (unsigned long k = 0; k < count; ++k)
        if (!k || memcmp(records[k].record, records[k - 1].record, sizeof(records[k].record)))
            first[records[k].position] = 1;
    printf("%s {\"id\":\"%s\",\"index\":%u,\"count\":%lu,\"records\":[", tag, id, i, count);
    int comma = 0;
    for (unsigned long k = 0; k < count; ++k) {
        if (!first[k]) continue;
        const unsigned long *r = area + 1 + 4 * k;
        printf("%s[%lu,\"0x%lx\",\"0x%lx\",\"0x%lx\"]", comma ? "," : "", r[0], r[1], r[2], r[3]);
        comma = 1;
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
        for (unsigned long k = 0; k < count;) {
            unsigned long *r = area + 1 + 4 * k;
            if ((r[0] >> 63) && ((r[0] >> 32) & 0xffff) == CHOICE_MAGIC + 1)
                fail(t->id, i, "coverage_failure", "malformed_choice_record");   /* payload without header */
            if (!(r[0] >> 63) || ((r[0] >> 32) & 0xffff) != CHOICE_MAGIC) {
                if (kept != k) memmove(area + 1 + 4 * kept, r, 4 * sizeof(*r));
                ++kept; ++k; continue;
            }
            unsigned long n = r[0] & 0xffff, nrec = 1 + (n + 2) / 3;
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
 * sort (pc, position) pairs, mark first positions, then print the marked PCs
 * in execution order. */
static void print_pcs(const char *tag, const char *id, unsigned i, const unsigned long *area, unsigned long count)
{
    for (unsigned long j = 0; j < count; ++j) {
        order[j].pc = area[j + 1];
        order[j].position = j;
    }
    qsort(order, count, sizeof(*order), compare_occurrence);
    memset(first, 0, count);
    for (unsigned long j = 0; j < count; ++j)
        if (!j || order[j].pc != order[j - 1].pc) first[order[j].position] = 1;
    printf("%s {\"id\":\"%s\",\"index\":%u,\"count\":%lu,\"pcs\":[", tag, id, i, count);
    int comma = 0;
    for (unsigned long j = 0; j < count; ++j) {
        if (!first[j]) continue;
        printf("%s\"0x%lx\"", comma ? "," : "", area[j + 1]);
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

/* A datagram's (family, length, message type, bytes) as JSON; the message
 * type is the first little-endian u32 of a WireGuard message. */
static int print_datagram(int comma, int family, long n)
{
    unsigned type = n >= 4 ? (unsigned)observe_buffer[0] | (unsigned)observe_buffer[1] << 8 |
                             (unsigned)observe_buffer[2] << 16 | (unsigned)observe_buffer[3] << 24 : 0;
    printf("%s[%d,%ld,%u,\"", comma ? "," : "", family, n, type);
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
    if (!error) error = nl_receive(rtnl, 0, NULL, 0);
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
    for (int family = AF_INET; family; family = family == AF_INET ? AF_INET6 : 0) {
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
                     !first && family == AF_INET ? -EEXIST : 0);
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
                     first ? "default_route_via_wg0" : "default_route_via_wg0_after_down", 0);
    }
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
    printf("\"stats\":{\"tx_errors\":%llu,\"tx_dropped\":%llu,\"rx_frame_errors\":%llu,\"rx_length_errors\":%llu}",
           (unsigned long long)stats->tx_errors, (unsigned long long)stats->tx_dropped,
           (unsigned long long)stats->rx_frame_errors, (unsigned long long)stats->rx_length_errors);
    if (close(rtnl)) fail(id, index, "environment_failure", "stats_close");
}

/* After wg_observe's recvfrom: drain both listeners and read the counters.
 * The comparison-mode child does the same, so both children end in the same
 * state; only the PC-mode child reports. */
static void observe(const struct trace *t, unsigned i, long first, int comparisons)
{
    if (!comparisons) printf("LEANUX_WGOBS {\"id\":\"%s\",\"index\":%u,\"datagrams\":[", t->id, i);
    int comma = 0;
    if (first >= 0 && !comparisons) comma = print_datagram(comma, 4, first);
    for (int family = 4; family <= 6; family += 2) {
        for (;;) {
            long n = recv(family == 4 ? LISTEN4_FD : LISTEN6_FD, observe_buffer, sizeof(observe_buffer), MSG_DONTWAIT);
            if (n < 0) {
                if (errno != EAGAIN) fail(t->id, i, "environment_failure", "drain_listener");
                break;
            }
            if (!comparisons) comma = print_datagram(comma, family, n);
        }
    }
    if (!comparisons) printf("],\"replies\":[");
    /* What the sender received (wg0's datagrams to it, and inner packets
     * delivered to it): recvfrom's source as the IPv6 socket reports it
     * (family, address as hex, port; an IPv4 source appears v4-mapped),
     * then the length, the WireGuard message type, the receiver index
     * (bytes 8-11, little-endian) and the bytes. */
    comma = 0;
    for (;;) {
        struct sockaddr_in6 source;
        socklen_t source_len = sizeof(source);
        memset(&source, 0, sizeof(source));
        long n = recvfrom(SEND_FD, observe_buffer, sizeof(observe_buffer), MSG_DONTWAIT | MSG_TRUNC,
                          (struct sockaddr *)&source, &source_len);
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
        printf("\",%u,%ld,%u,%u,\"", (unsigned)ntohs(source.sin6_port), n, type, receiver);
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
    if (!dispatch.n) fail(t->id, -1, "invalid_input", "wire_dispatch");
    if (ioctl(fd, KCOV_LEANUX_DISPATCH_LOAD, &dispatch)) fail(t->id, -1, "coverage_failure", "load_dispatch");
    pid_t child = fork();
    if (child < 0) fail(t->id, -1, "environment_failure", "fork_trace");
    if (child) {
        int status;
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

static void execute(const struct trace *t, int input_fd, int comparisons)
{
    struct observation result[MAX_OPS] = {{0}};
    if (close(input_fd)) fail(t->id, -1, "environment_failure", "close_input");
    /* The parent's watchdog: SIGALRM's handler is the parent's, not ours; and
     * this child leads its own process group, so the watchdog's kill reaches
     * a network trace's trace process too. */
    if (signal(SIGALRM, SIG_DFL) == SIG_ERR) fail(t->id, -1, "environment_failure", "reset_sigalrm");
    if (setpgid(0, 0)) fail(t->id, -1, "environment_failure", "setpgid");
    unsigned long *remote = t->net ? enable_remote(t, comparisons) : NULL;
    if (t->net) network_fixture(t->id, t->net == 2);
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
        if (socket(AF_INET, SOCK_DGRAM, 0) != LISTEN4_FD || bind(LISTEN4_FD, (struct sockaddr *)&a4, sizeof(a4)))
            fail(t->id, -1, "environment_failure", "listener4_at_4");
        if (socket(AF_INET6, SOCK_DGRAM, 0) != LISTEN6_FD ||
            setsockopt(LISTEN6_FD, IPPROTO_IPV6, IPV6_V6ONLY, &one, sizeof(one)) ||
            bind(LISTEN6_FD, (struct sockaddr *)&a6, sizeof(a6)))
            fail(t->id, -1, "environment_failure", "listener6_at_5");
        int zero = 0;
        struct sockaddr_in6 from = {.sin6_family = AF_INET6, .sin6_port = htons(SENDER_PORT), .sin6_addr = IN6ADDR_ANY_INIT};
        /* D2: the IP packets the sender routes into wg0 are determined by
         * the trace (Env.xmitPacket, docs/2026-10-04-d2-data-plane.md section
         * 2). IP_PMTUDISC_DO sets DF and clears ignore_df, so an unconnected
         * socket's IPv4 id is 0 rather than drawn from the jiffies-based
         * ident generator; IPV6_AUTOFLOWLABEL = 0 keeps the flow label 0
         * rather than a hash under a boot-time secret. */
        int pmtudisc = IP_PMTUDISC_DO;
        if (socket(AF_INET6, SOCK_DGRAM, 0) != SEND_FD ||
            setsockopt(SEND_FD, IPPROTO_IPV6, IPV6_V6ONLY, &zero, sizeof(zero)) ||
            setsockopt(SEND_FD, IPPROTO_IP, IP_MTU_DISCOVER, &pmtudisc, sizeof(pmtudisc)) ||
            setsockopt(SEND_FD, IPPROTO_IPV6, IPV6_AUTOFLOWLABEL, &zero, sizeof(zero)) ||
            bind(SEND_FD, (struct sockaddr *)&from, sizeof(from)))
            fail(t->id, -1, "environment_failure", "sender_at_6");
        /* The generic-netlink socket replaces the last filler; no SOCK_CLOEXEC,
         * so every fixture descriptor has close-on-exec clear. */
        if (socket(AF_NETLINK, SOCK_RAW, NETLINK_GENERIC) != NETLINK_FD)
            fail(t->id, -1, "environment_failure", "genl_socket_at_7");
        resolve_wireguard_family(t->id, NETLINK_FD);
        if (wg_exists) resolve_wg_ifindex(t->id, -1);
    }
    struct rlimit limit = {t->rlimit, t->rlimit}, actual;
    if (setrlimit(RLIMIT_NOFILE, &limit) || getrlimit(RLIMIT_NOFILE, &actual) || actual.rlim_cur != t->rlimit || actual.rlim_max != t->rlimit)
        fail(t->id, -1, "environment_failure", "rlimit_nofile");
    if (!comparisons) printf("LEANUX_FIXTURE {\"id\":\"%s\",\"reserved\":[0,1,2,3,4,5,6,7],\"free\":[8,%u],\"rlimit\":[%u,%u]}\n", t->id, t->rlimit - 1, t->rlimit, t->rlimit);
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
        if (((op->code >= OP_WG_UP && op->code <= OP_WG_INJECT) || IS_LIFECYCLE_OP(op->code)) && !t->net)
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
        /* E-B: the flood's socket, io_uring ring and SQEs are prepared before
         * the window (their inode/fd setup draws non-WireGuard clock records);
         * only io_uring_enter runs in the window. */
        struct flood_state flood;
        int flood_ready = 0;
        if (op->code == OP_WG_FLOOD) {
            if (!t->net) fail(t->id, i, "invalid_input", "wireguard_without_network_fixture");
            if (flood_prep(&flood, (unsigned)op->b, (unsigned)op->a, op->payload, op->payload_len))
                fail(t->id, i, "environment_failure", "flood_prepare");
            flood_ready = 1;
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
            if (!error) error = nl_receive(NETLINK_FD, GENL_HDRLEN, op->code == OP_WG_GET ? dump_hex : NULL, sizeof(dump_hex));
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
            if (op->payload_len == sizeof(to.sin6_addr))
                ret = syscall(SYS_sendto, SEND_FD, "leux", 4, 0, &to, sizeof(to));
            else
                ret = syscall(SYS_sendto, SEND_FD, op->payload + sizeof(to.sin6_addr),
                              op->payload_len - sizeof(to.sin6_addr), 0, &to, sizeof(to));
            break;
        }
        case OP_WG_INJECT: {
            /* A WireGuard message to wg0's port on 127.0.0.1 or ::1 (the
             * fixture's sender; IPv4 as v4-mapped). */
            struct sockaddr_in6 to = {.sin6_family = AF_INET6, .sin6_port = htons((uint16_t)op->b)};
            if (op->a == 4) {
                to.sin6_addr.s6_addr[10] = to.sin6_addr.s6_addr[11] = 0xff;
                to.sin6_addr.s6_addr[12] = 127;
                to.sin6_addr.s6_addr[15] = 1;
            } else {
                to.sin6_addr.s6_addr[15] = 1;
            }
            ret = syscall(SYS_sendto, SEND_FD, op->payload, op->payload_len, 0, &to, sizeof(to));
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
        case OP_WG_CREATE: case OP_WG_DELETE: {
            /* L: RTM_NEWLINK (wg_newlink, register_netdevice) or RTM_DELLINK
             * (unregister, netdev_run_todo, wg_destruct), both complete
             * inside send(); recv() reads the acknowledgement, whose error
             * code is the result. */
            int error = nl_send(lifecycle_fd, op->code == OP_WG_CREATE ? RTM_NEWLINK : RTM_DELLINK,
                                op->code == OP_WG_CREATE ? NEWLINK_FLAGS : NLM_F_REQUEST | NLM_F_ACK, 0, lifecycle_body,
                                lifecycle_len, 0);
            if (!error) error = nl_receive(lifecycle_fd, 0, NULL, 0);
            if (error < 0) { errno = -error; ret = -1; } else ret = 0;
            break;
        }
        case OP_WG_DOWN: {
            /* L: dev_change_flags(wg0, flags & ~IFF_UP) -> wg_stop. */
            struct ifreq request = up_request;
            ret = syscall(SYS_ioctl, SEND_FD, SIOCSIFFLAGS, &request);
            break;
        }
        case OP_WG_OBSERVE:
            /* The first datagram at the IPv4 listener, if any; the rest are
             * drained after coverage stops. */
            ret = syscall(SYS_recvfrom, LISTEN4_FD, observe_buffer, sizeof(observe_buffer), MSG_DONTWAIT, NULL, NULL);
            break;
        default: fail(t->id, i, "invalid_input", "wire_opcode");
        }
        int captured_errno = errno;
        unsigned long count = __atomic_load_n(&coverage[0], __ATOMIC_RELAXED);
        /* close the flood's socket and ring after the task count is captured
         * (the packets are already queued in wg0; the worker drains them in the
         * post-op wait regardless) so the fd teardown is outside the window. */
        if (flood_ready) flood_cleanup(&flood);
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
        if (op->code == OP_WG_UP && ret == 0 && !was_up) {
            if (!up_seen) {
                went_up = up_started;
                up_seen = 1;
            }
            route_into_wg0(t->id, i, first_up);
            first_up = 0;
        }
        if (op->code == OP_WG_OBSERVE) observe(t, i, ret, comparisons);
        /* The handshake worker runs after the send returns. An operation
         * that can queue the handshake send worker (wg_set, wg_up, wg_xmit)
         * waits for it too, so the worker's remote section lands in it. */
        if (op->code == OP_WG_INJECT) usleep(OBSERVE_WAIT_US);
        if (op->code == OP_WG_SET || op->code == OP_WG_UP || op->code == OP_WG_XMIT) usleep(QUEUE_WAIT_US);
        /* E-B: wait for the receive worker to drain the flood (its discarded
         * section) in this operation's window (~1 ms drain, measured). Keep the
         * wait short: the following injection must reach the worker within the
         * one-second last_under_load decay (§4.1). */
        if (op->code == OP_WG_FLOOD) usleep(QUEUE_WAIT_US);
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
            print_records("LEANUX_CMP", t->id, i, coverage, count);
            if (remote) print_records("LEANUX_RCMP", t->id, i, remote, remote_count);
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
        if (t->net) delete_wg0(t->id);
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
    if (t->net) delete_wg0(t->id);
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
            sscanf(line, "T %80s %u %u %u %u", trace.id, &trace.count, &trace.rlimit, &trace.net, &trace.nsteer) != 5 ||
            trace.count < 1 || trace.count > MAX_OPS || trace.rlimit < 8 || trace.rlimit > 1024 || trace.net > 2 ||
            trace.nsteer > STEER_MAX)
            fail("batch", -1, "invalid_input", "wire_trace");
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
            if (op->code == OP_WG_SET || op->code == OP_WG_GET || op->code == OP_WG_XMIT || op->code == OP_WG_INJECT || op->code == OP_WG_FLOOD) {
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
