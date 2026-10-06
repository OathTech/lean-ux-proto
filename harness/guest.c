/* Linux observations only. Run inside the pinned QEMU guest, never on the host. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <linux/genetlink.h>
#include <linux/if_link.h>
#include <linux/kcov.h>
#include <linux/netlink.h>
#include <linux/rtnetlink.h>
#include <linux/wireguard.h>
#include <net/if.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <time.h>
#include <sched.h>
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
#define CAPACITY (64UL * 1024)
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
#define WG_IFINDEX 3
/* wg_observe waits this long for the handshake workers before it looks. */
#define OBSERVE_WAIT_US 400000
#define QUEUE_WAIT_US 100000
/* A wg_xmit payload: at most wg0's MTU (1420) less the IPv4 and UDP headers. */
#define MAX_XMIT_PAYLOAD 1392
/* Timers fire REKEY_TIMEOUT (5 s) after a handshake is sent; a trace must end
 * well before that, counted from wg_up in real time: the virtual advances
 * (wg_advance) are subtracted. */
#define REKEY_BOUND_NS 4000000000LL
/* D3 (docs/2026-10-05-d3-timers.md, section 4.3): wg_advance moves jiffies by
 * `ticks` (KCOV_LEANUX_TIME_ADVANCE on the trace's own KCOV descriptor); the
 * timekeeper (refined-jiffies) follows at the next tick, which also runs the
 * due timers. The guest first waits for that tick (the monotonic clock has
 * absorbed the jump: a sleep begun before it would end at that same tick),
 * then ADVANCE_WAIT_US for the callbacks' work and loopback delivery. */
#define KCOV_LEANUX_TIME_ADVANCE _IOW('c', 204, unsigned long)
#define ADVANCE_WAIT_US 100000
#define TICK_NS 4000000LL           /* CONFIG_HZ=250 */
#define EXPECTED_CLOCKSOURCE "refined-jiffies"
struct operation { unsigned code, kind, newkind, a, b; long long fd, newfd; uint64_t value;
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
#define DISPATCH_MAX 16
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
    char id[81]; unsigned count; unsigned rlimit; unsigned net; struct operation ops[MAX_OPS];
    unsigned nsteer; struct steer_entry steer[STEER_MAX];
};
static char line[4 * MAX_PAYLOAD];
struct observation { long ret; int error; unsigned char bytes[16]; };

static void fail(const char *id, int index, const char *kind, const char *detail)
{
    printf("LEANUX_ERROR {\"id\":\"%s\",\"index\":%d,\"kind\":\"%s\",\"detail\":\"%s\",\"errno\":%d}\n",
           id, index, kind, detail, errno);
    fflush(stdout);
    _exit(1);
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

/* Fresh network namespace with a down `wg0`, created over a temporary
 * rtnetlink socket that is closed again before the fixture descriptors are
 * opened, so the descriptor-table history matches the plain fixture. */
static void network_fixture(const char *id)
{
    if (unshare(CLONE_NEWNET)) fail(id, -1, "environment_failure", "unshare_net");
    int rtnl = socket(AF_NETLINK, SOCK_RAW | SOCK_CLOEXEC, NETLINK_ROUTE);
    if (rtnl < 0) fail(id, -1, "environment_failure", "rtnetlink_socket");
    unsigned char payload[256];
    size_t len = sizeof(struct ifinfomsg);
    memset(payload, 0, sizeof(payload));
    attr(payload, &len, IFLA_IFNAME, "wg0", 4);
    size_t linkinfo = len;
    attr(payload, &len, IFLA_LINKINFO | NLA_F_NESTED, "", 0);
    attr(payload, &len, IFLA_INFO_KIND, "wireguard", 10);
    ((struct nlattr *)(payload + linkinfo))->nla_len = len - linkinfo;
    if (nl_send(rtnl, RTM_NEWLINK, NLM_F_REQUEST | NLM_F_ACK | NLM_F_CREATE | NLM_F_EXCL, 0, payload, len, 0) ||
        nl_receive(rtnl, 0, NULL, 0))
        fail(id, -1, "environment_failure", "create_wg0");
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
    int rtnl = socket(AF_NETLINK, SOCK_RAW | SOCK_CLOEXEC, NETLINK_ROUTE);
    if (rtnl < 0) fail(id, -1, "environment_failure", "rtnetlink_socket_teardown");
    unsigned char payload[64];
    size_t len = sizeof(struct ifinfomsg);
    memset(payload, 0, sizeof(payload));
    attr(payload, &len, IFLA_IFNAME, "wg0", 4);
    if (nl_send(rtnl, RTM_DELLINK, NLM_F_REQUEST | NLM_F_ACK, 0, payload, len, 0) || nl_receive(rtnl, 0, NULL, 0))
        fail(id, -1, "environment_failure", "delete_wg0");
    if (close(rtnl)) fail(id, -1, "environment_failure", "close_rtnetlink_teardown");
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

static long resolve(unsigned kind, long long value, const struct observation *results, unsigned i)
{
    if (!kind) return (long)(int32_t)value;
    if (kind != 1 || value < 0 || (unsigned long long)value >= i) return -1;
    return results[value].ret >= 0 ? results[value].ret : -1;
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
static int up_seen;
/* the virtual time the trace's advances added to CLOCK_BOOTTIME */
static long long advanced_ns;

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
                         const char *what)
{
    if (nl_send(rtnl, type, NLM_F_REQUEST | NLM_F_ACK | NLM_F_CREATE | NLM_F_EXCL, 0, body, len, 0) ||
        nl_receive(rtnl, 0, NULL, 0))
        fail(id, index, "environment_failure", what);
}

static void route_into_wg0(const char *id, unsigned index)
{
    int rtnl = socket(AF_NETLINK, SOCK_RAW, NETLINK_ROUTE);
    if (rtnl < 0) fail(id, index, "environment_failure", "route_socket");
    unsigned char body[128];
    uint32_t wg = WG_IFINDEX;
    for (int family = AF_INET; family; family = family == AF_INET ? AF_INET6 : 0) {
        size_t len = sizeof(struct ifaddrmsg);
        memset(body, 0, sizeof(body));
        struct ifaddrmsg *ifa = (struct ifaddrmsg *)body;
        ifa->ifa_family = family;
        ifa->ifa_index = WG_IFINDEX;
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
        rtnl_request(rtnl, id, index, RTM_NEWADDR, body, len, "address_on_wg0");
        len = sizeof(struct rtmsg);
        memset(body, 0, sizeof(body));
        struct rtmsg *rt = (struct rtmsg *)body;
        rt->rtm_family = family;
        rt->rtm_table = RT_TABLE_MAIN;
        rt->rtm_protocol = RTPROT_STATIC;
        rt->rtm_scope = RT_SCOPE_LINK;
        rt->rtm_type = RTN_UNICAST;
        attr(body, &len, RTA_OIF, &wg, sizeof(wg));
        rtnl_request(rtnl, id, index, RTM_NEWROUTE, body, len, "default_route_via_wg0");
    }
    if (close(rtnl)) fail(id, index, "environment_failure", "route_close");
}

/* wg0's transmit counters and receive error counters over a temporary rtnetlink socket, which is closed
 * again (without SOCK_CLOEXEC, see route_into_wg0). */
static void print_stats(const char *id, unsigned index)
{
    int rtnl = socket(AF_NETLINK, SOCK_RAW, NETLINK_ROUTE);
    if (rtnl < 0) fail(id, index, "environment_failure", "stats_socket");
    struct ifinfomsg request = {.ifi_family = AF_UNSPEC, .ifi_index = WG_IFINDEX};
    if (nl_send(rtnl, RTM_GETLINK, NLM_F_REQUEST, 0, (unsigned char *)&request, sizeof(request), 0))
        fail(id, index, "environment_failure", "stats_request");
    ssize_t n = recv(rtnl, nl_buffer, sizeof(nl_buffer), 0);
    struct nlmsghdr *h = (struct nlmsghdr *)nl_buffer;
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

static void execute(const struct trace *t, int input_fd, int comparisons)
{
    struct observation result[MAX_OPS] = {{0}};
    if (close(input_fd)) fail(t->id, -1, "environment_failure", "close_input");
    unsigned long *remote = t->net ? enable_remote(t, comparisons) : NULL;
    if (t->net) network_fixture(t->id);
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
    if (ioctl(coverage_fd, KCOV_ENABLE, comparisons ? KCOV_TRACE_CMP : KCOV_TRACE_PC))
        fail(t->id, -1, "coverage_failure", "enable_kcov");
    for (unsigned i = 0; i < t->count; ++i) {
        const struct operation *op = &t->ops[i];
        long fd = resolve(op->kind, op->fd, result, i);
        long newfd = resolve(op->newkind, op->newfd, result, i);
        unsigned char buffer[16];
        memset(buffer, op->code == 5 ? 0xa5 : 0, sizeof(buffer));
        if (op->code == 6)
            for (unsigned j = 0; j < 8; ++j) buffer[j] = (unsigned char)(op->value >> (8 * j));
        if ((op->code >= 10) && !t->net) fail(t->id, i, "invalid_input", "wireguard_without_network_fixture");
        struct ifreq up_request;
        if (op->code == 10) {
            memset(&up_request, 0, sizeof(up_request));
            strcpy(up_request.ifr_name, "wg0");
            if (ioctl(SEND_FD, SIOCGIFFLAGS, &up_request)) fail(t->id, i, "environment_failure", "get_wg0_flags");
            up_request.ifr_flags |= IFF_UP;
        }
        if (op->code == 12) usleep(OBSERVE_WAIT_US);
        /* before the coverage window: the clock the advance's wait watches */
        struct timespec before_advance = {0};
        if (op->code == 14 && clock_gettime(CLOCK_MONOTONIC, &before_advance))
            fail(t->id, i, "environment_failure", "advance_clock");
        __atomic_store_n(&coverage[0], 0, __ATOMIC_RELAXED);
        if (remote) __atomic_store_n(&remote[0], 0, __ATOMIC_RELAXED);
        errno = 0;
        long ret;
        switch (op->code) {
        case 1: ret = syscall(SYS_eventfd2, (unsigned long)op->a, (unsigned long)op->b); break;
        case 2: ret = syscall(SYS_dup, fd); break;
        case 3: ret = syscall(SYS_dup3, fd, newfd, (unsigned long)op->b); break;
        case 4: ret = syscall(SYS_close, fd); break;
        case 5: ret = syscall(SYS_read, fd, buffer, (unsigned long)op->a); break;
        case 6: ret = syscall(SYS_write, fd, buffer, (unsigned long)op->a); break;
        case 7: ret = syscall(SYS_fcntl, fd, (unsigned long)op->a, (unsigned long)op->b); break;
        case 8: case 9: {
            /* WG_CMD_SET_DEVICE (acknowledged) or a WG_CMD_GET_DEVICE dump; the
             * kernel's error code becomes the operation's result. */
            if (!t->net) fail(t->id, i, "invalid_input", "wireguard_without_network_fixture");
            int error = nl_send(NETLINK_FD, wg_family,
                                op->code == 8 ? NLM_F_REQUEST | NLM_F_ACK : NLM_F_REQUEST | NLM_F_DUMP,
                                op->code == 8 ? WG_CMD_SET_DEVICE : WG_CMD_GET_DEVICE, op->payload, op->payload_len, 1);
            if (!error) error = nl_receive(NETLINK_FD, GENL_HDRLEN, op->code == 9 ? dump_hex : NULL, sizeof(dump_hex));
            if (error < 0) { errno = -error; ret = -1; } else ret = 0;
            break;
        }
        case 10: {
            /* dev_change_flags(wg0, flags | IFF_UP) -> wg_open. The current
             * flags were read before coverage started. */
            struct ifreq request = up_request;
            ret = syscall(SYS_ioctl, SEND_FD, SIOCSIFFLAGS, &request);
            break;
        }
        case 11: {
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
        case 13: {
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
        case 14: {
            /* D3: the virtual time advance, on this process's KCOV
             * descriptor (fd 3); the kernel records {jiffies before, after}
             * (kind 304) in the task stream. */
            unsigned long ticks = op->a;
            ret = syscall(SYS_ioctl, 3, KCOV_LEANUX_TIME_ADVANCE, &ticks);
            break;
        }
        case 12:
            /* The first datagram at the IPv4 listener, if any; the rest are
             * drained after coverage stops. */
            ret = syscall(SYS_recvfrom, LISTEN4_FD, observe_buffer, sizeof(observe_buffer), MSG_DONTWAIT, NULL, NULL);
            break;
        default: fail(t->id, i, "invalid_input", "wire_opcode");
        }
        int captured_errno = errno;
        unsigned long count = __atomic_load_n(&coverage[0], __ATOMIC_RELAXED);
        /* Outside the coverage window: the dump's attribute payloads. */
        if (op->code == 9 && !comparisons && ret == 0)
            printf("LEANUX_WG {\"id\":\"%s\",\"index\":%u,\"payloads\":[%s]}\n", t->id, i, dump_hex);
        if (op->code == 10 && ret == 0) {
            clock_gettime(CLOCK_BOOTTIME, &went_up);
            up_seen = 1;
            route_into_wg0(t->id, i);
        }
        if (op->code == 12) observe(t, i, ret, comparisons);
        /* The handshake worker runs after the send returns. An operation
         * that can queue the handshake send worker (wg_set, wg_up, wg_xmit)
         * waits for it too, so the worker's remote section lands in it. */
        if (op->code == 13) usleep(OBSERVE_WAIT_US);
        if (op->code == 8 || op->code == 10 || op->code == 11) usleep(QUEUE_WAIT_US);
        if (op->code == 14) {
            /* An advance that fails is not a trace operation the mirror can
             * follow: fail the trace. Then wait for the tick that absorbs the
             * jump (bounded: 1 s of real time), then ADVANCE_WAIT_US. */
            if (ret != 0) fail(t->id, i, "environment_failure", "time_advance");
            long long jump = (long long)op->a * TICK_NS;
            int polls = 0;
            for (;;) {
                struct timespec now;
                if (clock_gettime(CLOCK_MONOTONIC, &now)) fail(t->id, i, "environment_failure", "advance_clock");
                if ((now.tv_sec - before_advance.tv_sec) * 1000000000LL + (now.tv_nsec - before_advance.tv_nsec) >= jump)
                    break;
                if (++polls > 1000) fail(t->id, i, "environment_failure", "advance_not_absorbed");
                usleep(1000);
            }
            usleep(ADVANCE_WAIT_US);
            advanced_ns += jump;
        }
        if (up_seen) {
            struct timespec now;
            clock_gettime(CLOCK_BOOTTIME, &now);
            if ((now.tv_sec - went_up.tv_sec) * 1000000000LL + (now.tv_nsec - went_up.tv_nsec) - advanced_ns > REKEY_BOUND_NS)
                fail(t->id, i, "environment_failure", "trace_exceeds_rekey_bound");
        }
        /* KCOV stops counting once the buffer is full, so "full" is the last
         * value it can reach: CAPACITY - 1 PCs, or (CAPACITY - 1) / 4 records. */
        if (!count || count >= (comparisons ? (CAPACITY - 1) / 4 : CAPACITY - 1))
            fail(t->id, i, "coverage_failure", "empty_or_full_kcov");
        result[i].error = ret == -1 ? captured_errno : 0;
        result[i].ret = ret == -1 ? -captured_errno : ret;
        if (op->code == 5 && ret > 0) {
            if (ret > 16) fail(t->id, i, "environment_failure", "read_return_exceeds_buffer");
            memcpy(result[i].bytes, buffer, (size_t)ret);
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
    if (comparisons) {
        printf("LEANUX_CMP_RESULT {\"id\":\"%s\",\"rets\":[", t->id);
        for (unsigned i = 0; i < t->count; ++i) printf("%s%ld", i ? "," : "", result[i].ret);
        printf("],\"bytes\":[");
        for (unsigned i = 0; i < t->count; ++i) {
            printf("%s\"", i ? "," : "");
            if (t->ops[i].code == 5 && result[i].ret > 0)
                for (long j = 0; j < result[i].ret; ++j) printf("%02x", result[i].bytes[j]);
            printf("\"");
        }
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
        printf(",\"bytes\":\"");
        if (t->ops[i].code == 5 && result[i].ret > 0)
            for (long j = 0; j < result[i].ret; ++j) printf("%02x", result[i].bytes[j]);
        printf("\"}");
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

int main(int argc, char **argv)
{
    setvbuf(stdout, NULL, _IOLBF, 0);
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
            trace.count < 1 || trace.count > MAX_OPS || trace.rlimit < 8 || trace.rlimit > 1024 || trace.net > 1 ||
            trace.nsteer > STEER_MAX)
            fail("batch", -1, "invalid_input", "wire_trace");
        for (unsigned i = 0; i < trace.count; ++i) {
            struct operation *op = &trace.ops[i];
            int consumed = 0;
            if (!fgets(line, sizeof(line), input) || sscanf(line, "%u %u %lld %u %lld %u %u %" SCNu64 "%n",
                &op->code, &op->kind, &op->fd, &op->newkind, &op->newfd, &op->a, &op->b, &op->value, &consumed) != 8)
                fail(trace.id, i, "invalid_input", "wire_operation");
            op->payload_len = 0;
            if (op->code == 8 || op->code == 9 || op->code == 11 || op->code == 13) {
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
            if (waitpid(child, &status, 0) != child) fail(trace.id, -1, "environment_failure", "wait_child");
            if (!WIFEXITED(status) || WEXITSTATUS(status)) {
                printf("LEANUX_CHILD_FAILURE {\"id\":\"%s\",\"status\":%d}\n", trace.id, status);
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
