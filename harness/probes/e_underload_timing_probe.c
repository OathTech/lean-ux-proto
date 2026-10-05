/* THROWAWAY PROBE for workstream E arms B/C (docs/2026-10-05-e-dos.md), not the
 * oracle. Gates the "decay lever" design (audit C1/M4): the flood must run as a
 * fully-drained receive-worker section, then an injection in a SEPARATE section,
 * both while last_under_load's 1 s decay is still live. So the question is not
 * just "decay live" but "worker went idle AND decay still live", within 4 s.
 *
 * Measures, on the pinned kernel:
 *  A. the minimal flood (GSO, invalid-MAC1) that crosses 512 (accounting for
 *     inter-softirq drain): the smallest N for which a valid-MAC1 probe injected
 *     right after gets a cookie reply;
 *  B. the drain time of a 1024 invalid-MAC1 flood: the reply latency of a
 *     valid-MAC1 probe injected at D=0 (it sits behind the flood, so its reply
 *     arrives after the worker drains the flood -> T_drain);
 *  C. the distinct-section window: flood 1024 invalid, sleep D, inject 1 valid;
 *     for D > T_drain the worker is idle (a new section) -- does the probe still
 *     reply (decay live)? The max such D vs T_drain decides viability.
 *
 * Signal as in e_underload_probe.c: a valid-MAC1 initiation under load makes wg0
 * emit a MESSAGE_HANDSHAKE_COOKIE (type 3) reply. Invalid-MAC1 packets enqueue
 * (crossing 512) but are dropped (INVALID_MAC) with no reply and a fast drain. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <linux/genetlink.h>
#include <linux/if_link.h>
#include <linux/netlink.h>
#include <linux/rtnetlink.h>
#include <linux/udp.h>
#include <linux/wireguard.h>
#include <net/if.h>
#include <netinet/in.h>
#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

#ifndef UDP_SEGMENT
#define UDP_SEGMENT 103
#endif
#ifndef SOL_UDP
#define SOL_UDP 17
#endif
#define WG_PORT 51820
#define SRC_PORT 51998
#define SEG 148
#define GSO_SEGS 128

static const unsigned char PRIV[32] = {PRIV_BYTES};
static const unsigned char INIT[SEG] = {INIT_BYTES};   /* valid MAC1 */
static unsigned char BAD[SEG];                          /* invalid MAC1 */

static unsigned char nl_buffer[1 << 16];
static unsigned short wg_family;

static void die(const char *w) { fprintf(stderr, "PROBE_FAIL %s errno=%d\n", w, errno); exit(1); }

static void attr(unsigned char *b, size_t *len, unsigned short type, const void *d, size_t n)
{
    struct nlattr *a = (struct nlattr *)(b + *len);
    a->nla_len = NLA_HDRLEN + n; a->nla_type = type;
    memcpy(b + *len + NLA_HDRLEN, d, n); *len += NLA_ALIGN(a->nla_len);
}
static int nl_send(int fd, unsigned short type, unsigned short flags, unsigned char cmd,
                   const unsigned char *payload, size_t len, int genl)
{
    static unsigned char m[sizeof(struct nlmsghdr) + GENL_HDRLEN + 4096];
    struct nlmsghdr *h = (struct nlmsghdr *)m; size_t off = NLMSG_HDRLEN;
    memset(m, 0, sizeof(m));
    if (genl) { struct genlmsghdr *g = (struct genlmsghdr *)(m + off); g->cmd = cmd; g->version = WG_GENL_VERSION; off += GENL_HDRLEN; }
    memcpy(m + off, payload, len);
    h->nlmsg_len = off + len; h->nlmsg_type = type; h->nlmsg_flags = flags; h->nlmsg_seq = 1;
    return send(fd, m, h->nlmsg_len, 0) == (ssize_t)h->nlmsg_len ? 0 : -errno;
}
static int nl_receive(int fd)
{
    for (;;) {
        ssize_t n = recv(fd, nl_buffer, sizeof(nl_buffer), 0);
        if (n < 0) return -errno;
        for (struct nlmsghdr *h = (struct nlmsghdr *)nl_buffer; NLMSG_OK(h, n); h = NLMSG_NEXT(h, n)) {
            if (h->nlmsg_type == NLMSG_ERROR) return ((struct nlmsgerr *)NLMSG_DATA(h))->error;
            if (h->nlmsg_type == NLMSG_DONE) return *(int *)NLMSG_DATA(h);
        }
    }
}
static void resolve_family(int fd)
{
    unsigned char p[64]; size_t len = 0;
    attr(p, &len, CTRL_ATTR_FAMILY_NAME, WG_GENL_NAME, sizeof(WG_GENL_NAME));
    if (nl_send(fd, GENL_ID_CTRL, NLM_F_REQUEST, CTRL_CMD_GETFAMILY, p, len, 2)) die("getfamily");
    ssize_t n = recv(fd, nl_buffer, sizeof(nl_buffer), 0);
    struct nlmsghdr *h = (struct nlmsghdr *)nl_buffer;
    if (n < 0 || !NLMSG_OK(h, n)) die("family_reply");
    unsigned char *a = (unsigned char *)NLMSG_DATA(h) + GENL_HDRLEN;
    size_t rem = h->nlmsg_len - NLMSG_HDRLEN - GENL_HDRLEN;
    while (rem >= NLA_HDRLEN) {
        struct nlattr *na = (struct nlattr *)a;
        if (na->nla_len < NLA_HDRLEN || na->nla_len > rem) break;
        if ((na->nla_type & NLA_TYPE_MASK) == CTRL_ATTR_FAMILY_ID) { memcpy(&wg_family, a + NLA_HDRLEN, 2); return; }
        a += NLA_ALIGN(na->nla_len); rem -= NLA_ALIGN(na->nla_len) < rem ? NLA_ALIGN(na->nla_len) : rem;
    }
    die("family_id");
}
static void setup(void)
{
    if (unshare(CLONE_NEWNET)) die("unshare");
    int rtnl = socket(AF_NETLINK, SOCK_RAW | SOCK_CLOEXEC, NETLINK_ROUTE);
    unsigned char p[256]; size_t len = sizeof(struct ifinfomsg);
    memset(p, 0, sizeof(p));
    attr(p, &len, IFLA_IFNAME, "wg0", 4);
    size_t li = len; attr(p, &len, IFLA_LINKINFO | NLA_F_NESTED, "", 0);
    attr(p, &len, IFLA_INFO_KIND, "wireguard", 10);
    ((struct nlattr *)(p + li))->nla_len = len - li;
    if (nl_send(rtnl, RTM_NEWLINK, NLM_F_REQUEST | NLM_F_ACK | NLM_F_CREATE | NLM_F_EXCL, 0, p, len, 0) || nl_receive(rtnl)) die("create");
    struct ifinfomsg up = {.ifi_family = AF_UNSPEC, .ifi_index = 1, .ifi_flags = IFF_UP, .ifi_change = IFF_UP};
    if (nl_send(rtnl, RTM_NEWLINK, NLM_F_REQUEST | NLM_F_ACK, 0, (unsigned char *)&up, sizeof(up), 0) || nl_receive(rtnl)) die("lo_up");
    close(rtnl);
    int genl = socket(AF_NETLINK, SOCK_RAW, NETLINK_GENERIC);
    resolve_family(genl);
    unsigned char q[256]; size_t ql = 0; uint16_t port = WG_PORT;
    attr(q, &ql, WGDEVICE_A_IFNAME, "wg0", 4);
    attr(q, &ql, WGDEVICE_A_PRIVATE_KEY, PRIV, sizeof(PRIV));
    attr(q, &ql, WGDEVICE_A_LISTEN_PORT, &port, sizeof(port));
    if (nl_send(genl, wg_family, NLM_F_REQUEST | NLM_F_ACK, WG_CMD_SET_DEVICE, q, ql, 1) || nl_receive(genl)) die("wg_set");
    int fs = socket(AF_INET, SOCK_DGRAM, 0);
    struct ifreq r; memset(&r, 0, sizeof(r)); strcpy(r.ifr_name, "wg0");
    if (ioctl(fs, SIOCGIFFLAGS, &r)) die("get_flags");
    r.ifr_flags |= IFF_UP;
    if (ioctl(fs, SIOCSIFFLAGS, &r)) die("set_up");
    close(fs);
}

static double now_ms(void)
{
    struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec * 1000.0 + t.tv_nsec / 1e6;
}
static int drain(int s)
{
    unsigned char b[2048]; int c = 0;
    for (;;) { ssize_t n = recv(s, b, sizeof(b), MSG_DONTWAIT); if (n < 0) break; if (n == 64 && b[0] == 3) c++; }
    return c;
}
/* GSO flood of N copies of `tmpl`, as ceil(N/128) datagrams via sendmmsg. */
static void flood(int s, const unsigned char *tmpl, int n)
{
    static unsigned char buf[SEG * GSO_SEGS];
    for (int i = 0; i < GSO_SEGS; i++) memcpy(buf + i * SEG, tmpl, SEG);
    int gso = SEG;
    if (setsockopt(s, SOL_UDP, UDP_SEGMENT, &gso, sizeof(gso))) die("udp_segment");
    int dgrams = (n + GSO_SEGS - 1) / GSO_SEGS;
    struct mmsghdr m[64]; struct iovec v[64];
    for (int i = 0; i < dgrams && i < 64; i++) {
        int segs = (i == dgrams - 1) ? (n - i * GSO_SEGS) : GSO_SEGS;
        v[i].iov_base = buf; v[i].iov_len = (size_t)segs * SEG;
        m[i].msg_hdr = (struct msghdr){0}; m[i].msg_hdr.msg_iov = &v[i]; m[i].msg_hdr.msg_iovlen = 1;
    }
    syscall(SYS_sendmmsg, s, m, dgrams < 64 ? dgrams : 64, 0);
    gso = 0; setsockopt(s, SOL_UDP, UDP_SEGMENT, &gso, sizeof(gso));
}
/* Inject one valid-MAC1 initiation; wait up to `timeout_ms` for its cookie
 * reply. Returns the reply latency in ms, or -1 if none. */
static double inject_wait(int s, double timeout_ms)
{
    double t0 = now_ms();
    if (send(s, INIT, SEG, 0) != SEG) die("inject_send");
    for (;;) {
        double el = now_ms() - t0;
        if (el > timeout_ms) return -1;
        int c = drain(s);
        if (c > 0) return now_ms() - t0;
        usleep(5000);
    }
}
static void settle(int s) { drain(s); sleep(2); drain(s); }   /* clear last_under_load decay */

/* Harvest all cookie replies a burst produced (settle, drain, repeat). */
static int harvest(int s)
{
    int total = 0, idle = 0;
    for (int r = 0; r < 100 && idle < 3; r++) { usleep(50000); int g = drain(s); total += g; idle = g ? 0 : idle + 1; if (total > 200000) break; }
    return total;
}

#include <sys/mman.h>
#include <linux/io_uring.h>
/* Submit n IORING_OP_SEND of `tmpl` in one enter (no per-send cond_resched). */
static long iouring_flood(int sockfd, const unsigned char *tmpl, int n)
{
    struct io_uring_params pp; memset(&pp, 0, sizeof(pp));
    int ring = syscall(SYS_io_uring_setup, n, &pp);
    if (ring < 0) return -1;
    size_t sqsz = pp.sq_off.array + pp.sq_entries * sizeof(unsigned);
    void *sq = mmap(0, sqsz, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring, IORING_OFF_SQ_RING);
    struct io_uring_sqe *sqes = mmap(0, pp.sq_entries * sizeof(struct io_uring_sqe),
                                     PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring, IORING_OFF_SQES);
    if (sq == MAP_FAILED || sqes == MAP_FAILED) { close(ring); return -2; }
    unsigned *ktail = (unsigned *)((char *)sq + pp.sq_off.tail);
    unsigned *karray = (unsigned *)((char *)sq + pp.sq_off.array);
    unsigned mask = *(unsigned *)((char *)sq + pp.sq_off.ring_mask);
    int submit = n < (int)pp.sq_entries ? n : (int)pp.sq_entries;
    for (int i = 0; i < submit; i++) {
        struct io_uring_sqe *e = &sqes[i]; memset(e, 0, sizeof(*e));
        e->opcode = IORING_OP_SEND; e->fd = sockfd; e->addr = (unsigned long)tmpl; e->len = SEG;
        karray[i & mask] = i;
    }
    __atomic_store_n(ktail, submit, __ATOMIC_RELEASE);
    long r = syscall(SYS_io_uring_enter, ring, submit, 0, 0, 0, 0);
    close(ring);
    return r < 0 ? -3 : r;
}

int main(void)
{
    unsigned char seed;
    if (syscall(SYS_getrandom, &seed, 1, 0) != 1) die("getrandom");
    memcpy(BAD, INIT, SEG); memset(BAD + 116, 0xff, 16);   /* corrupt MAC1 */
    setup();
    int s = socket(AF_INET, SOCK_DGRAM, 0);
    struct sockaddr_in src = {.sin_family = AF_INET, .sin_port = htons(SRC_PORT)};
    src.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    if (bind(s, (struct sockaddr *)&src, sizeof(src))) die("bind");
    struct sockaddr_in dst = {.sin_family = AF_INET, .sin_port = htons(WG_PORT)};
    dst.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    if (connect(s, (struct sockaddr *)&dst, sizeof(dst))) die("connect");
    int rb = 8 << 20; setsockopt(s, SOL_SOCKET, SO_RCVBUF, &rb, sizeof(rb));

    /* Q0 sanity + variability: a VALID-MAC1 GSO flood of 1024 crosses and
     * replies (as e_underload_probe.c saw); run 3x for the reply spread. */
    for (int rep = 0; rep < 3; rep++) {
        settle(s);
        flood(s, INIT, 1024);
        int c = harvest(s);
        printf("LEANUX_TIMING {\"test\":\"valid_gso_1024\",\"rep\":%d,\"cookie_replies\":%d}\n", rep, c);
        fflush(stdout);
    }

    /* Q1 cheap crossing: can an INVALID-MAC1 (reply-free, fast-drain) flood set
     * last_under_load? Probe each mechanism with a following valid injection. */
    struct { const char *name; int mech; int n; } cheap[] = {
        {"gso_invalid_1024", 0, 1024}, {"gso_invalid_4096", 0, 4096},
        {"iouring_invalid_1024", 1, 1024}, {"iouring_invalid_4096", 1, 4096},
        {"iouring_invalid_16384", 1, 16384},
    };
    for (unsigned i = 0; i < sizeof(cheap) / sizeof(cheap[0]); i++) {
        settle(s);
        long sent = 0;
        if (cheap[i].mech == 0) { flood(s, BAD, cheap[i].n); sent = cheap[i].n; }
        else sent = iouring_flood(s, BAD, cheap[i].n);
        double lat = inject_wait(s, 1500);
        printf("LEANUX_TIMING {\"test\":\"cheap_cross\",\"mech\":\"%s\",\"sent\":%ld,\"probe_reply\":%s}\n",
               cheap[i].name, sent, lat >= 0 ? "true" : "false");
        fflush(stdout);
    }

    /* Q2 distinct-section viability (audit C1): io_uring invalid flood crosses
     * cheaply; measure its drain time (D=0 probe latency) and whether a valid
     * injection at D > drain (worker surely idle, a NEW section) still replies
     * (decay live), all inside the 4 s bound. */
    settle(s);
    iouring_flood(s, BAD, 1024);
    double tdrain = inject_wait(s, 3000);
    printf("LEANUX_TIMING {\"test\":\"iouring_drain_1024\",\"t_drain_ms\":%.0f}\n", tdrain);
    fflush(stdout);
    int ds[] = {0, 50, 100, 200, 300, 500, 700, 900, 1200};
    double max_d_reply = -1;
    for (unsigned i = 0; i < sizeof(ds) / sizeof(ds[0]); i++) {
        settle(s);
        iouring_flood(s, BAD, 1024);
        usleep(ds[i] * 1000);
        double lat = inject_wait(s, 1500);
        int idle = (tdrain >= 0 && ds[i] > tdrain);
        printf("LEANUX_TIMING {\"test\":\"iouring_window\",\"delay_ms\":%d,\"reply\":%s,\"latency_ms\":%.0f,\"worker_idle\":%s}\n",
               ds[i], lat >= 0 ? "true" : "false", lat, idle ? "true" : "false");
        fflush(stdout);
        if (lat >= 0) max_d_reply = ds[i];
    }
    printf("LEANUX_TIMING_SUMMARY {\"iouring_t_drain_ms\":%.0f,\"iouring_max_delay_with_reply_ms\":%.0f,"
           "\"distinct_section_viable\":%s}\n", tdrain, max_d_reply,
           (tdrain >= 0 && max_d_reply > tdrain) ? "true" : "false");

    printf("LEANUX_PROBE_DONE\n");
    fflush(stdout);
    return 0;
}
