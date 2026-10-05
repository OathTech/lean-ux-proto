/* THROWAWAY PROBE for workstream E (docs/2026-10-05-e-dos.md), not the oracle.
 *
 * Question: can a burst of injected handshakes push wg0's handshake_queue_len
 * past MAX_QUEUED_INCOMING_HANDSHAKES/8 = 512 on this single-CPU kernel, so the
 * `under_load` arm (receive.c:112) is taken? The audit (C1/C2) says UDP GSO lets
 * one sendmsg deliver up to 128 segments into one NET_RX softirq with no drain.
 *
 * Signal: a *valid-MAC1* handshake initiation processed while under_load makes
 * wg0 emit a MESSAGE_HANDSHAKE_COOKIE (type 3) reply to the source (cookie.c,
 * receive.c:126-132,139-143). So >=1 cookie reply = under_load was crossed. The
 * initiation bytes are precomputed on the host (a fixed private key, so wg0's
 * message_mac1_key = blake2s("mac1----" ‖ wg0_public) is known); the probe just
 * sets that key and blasts copies. No crypto in the guest.
 *
 * Mechanisms, each in a fresh queue state (2 s drain + the 1 s last_under_load
 * decay between them): GSO via sendmmsg, GSO via a send() loop, a 1024-wide
 * plain sendmmsg, and io_uring (best effort). Reports LEANUX_PROBE rows. */
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
#include <sys/mman.h>
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
#define SEG 148             /* sizeof(message_handshake_initiation) */
#define GSO_SEGS 128        /* UDP_MAX_SEGMENTS (include/linux/udp.h) */
#define GSO_DGRAMS 8        /* 8 * 128 = 1024 segments per burst */
#define PLAIN_DGRAMS 1024   /* UIO_MAXIOV */

/* Precomputed on the host (see the runner): a clamped private key and a
 * 148-byte initiation whose MAC1 is valid for that key's public. */
static const unsigned char PRIV[32] = {PRIV_BYTES};
static const unsigned char INIT[SEG] = {INIT_BYTES};

static unsigned char nl_buffer[1 << 16];
static unsigned short wg_family;

static void die(const char *what) { fprintf(stderr, "PROBE_FAIL %s errno=%d\n", what, errno); exit(1); }

static void attr(unsigned char *buf, size_t *len, unsigned short type, const void *data, size_t size)
{
    struct nlattr *a = (struct nlattr *)(buf + *len);
    a->nla_len = NLA_HDRLEN + size;
    a->nla_type = type;
    memcpy(buf + *len + NLA_HDRLEN, data, size);
    *len += NLA_ALIGN(a->nla_len);
}

static int nl_send(int fd, unsigned short type, unsigned short flags, unsigned char cmd,
                   const unsigned char *payload, size_t len, int genl)
{
    static unsigned char message[sizeof(struct nlmsghdr) + GENL_HDRLEN + 4096];
    struct nlmsghdr *header = (struct nlmsghdr *)message;
    size_t offset = NLMSG_HDRLEN;
    memset(message, 0, sizeof(message));
    if (genl) {
        struct genlmsghdr *g = (struct genlmsghdr *)(message + offset);
        g->cmd = cmd;
        g->version = WG_GENL_VERSION;
        offset += GENL_HDRLEN;
    }
    memcpy(message + offset, payload, len);
    header->nlmsg_len = offset + len;
    header->nlmsg_type = type;
    header->nlmsg_flags = flags;
    header->nlmsg_seq = 1;
    return send(fd, message, header->nlmsg_len, 0) == (ssize_t)header->nlmsg_len ? 0 : -errno;
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
    unsigned char payload[64];
    size_t len = 0;
    attr(payload, &len, CTRL_ATTR_FAMILY_NAME, WG_GENL_NAME, sizeof(WG_GENL_NAME));
    if (nl_send(fd, GENL_ID_CTRL, NLM_F_REQUEST, CTRL_CMD_GETFAMILY, payload, len, 2)) die("genl_getfamily");
    ssize_t n = recv(fd, nl_buffer, sizeof(nl_buffer), 0);
    struct nlmsghdr *h = (struct nlmsghdr *)nl_buffer;
    if (n < 0 || !NLMSG_OK(h, n)) die("genl_family_reply");
    unsigned char *attrs = (unsigned char *)NLMSG_DATA(h) + GENL_HDRLEN;
    size_t rem = h->nlmsg_len - NLMSG_HDRLEN - GENL_HDRLEN;
    while (rem >= NLA_HDRLEN) {
        struct nlattr *a = (struct nlattr *)attrs;
        if (a->nla_len < NLA_HDRLEN || a->nla_len > rem) break;
        if ((a->nla_type & NLA_TYPE_MASK) == CTRL_ATTR_FAMILY_ID) {
            memcpy(&wg_family, attrs + NLA_HDRLEN, sizeof(wg_family));
            return;
        }
        attrs += NLA_ALIGN(a->nla_len);
        rem -= NLA_ALIGN(a->nla_len) < rem ? NLA_ALIGN(a->nla_len) : rem;
    }
    die("genl_family_id");
}

static void create_wg0(void)
{
    if (unshare(CLONE_NEWNET)) die("unshare");
    int rtnl = socket(AF_NETLINK, SOCK_RAW | SOCK_CLOEXEC, NETLINK_ROUTE);
    if (rtnl < 0) die("rtnl_socket");
    unsigned char p[256];
    size_t len = sizeof(struct ifinfomsg);
    memset(p, 0, sizeof(p));
    attr(p, &len, IFLA_IFNAME, "wg0", 4);
    size_t li = len;
    attr(p, &len, IFLA_LINKINFO | NLA_F_NESTED, "", 0);
    attr(p, &len, IFLA_INFO_KIND, "wireguard", 10);
    ((struct nlattr *)(p + li))->nla_len = len - li;
    if (nl_send(rtnl, RTM_NEWLINK, NLM_F_REQUEST | NLM_F_ACK | NLM_F_CREATE | NLM_F_EXCL, 0, p, len, 0) ||
        nl_receive(rtnl)) die("create_wg0");
    struct ifinfomsg up = {.ifi_family = AF_UNSPEC, .ifi_index = 1, .ifi_flags = IFF_UP, .ifi_change = IFF_UP};
    if (nl_send(rtnl, RTM_NEWLINK, NLM_F_REQUEST | NLM_F_ACK, 0, (unsigned char *)&up, sizeof(up), 0) ||
        nl_receive(rtnl)) die("lo_up");
    close(rtnl);
}

static void configure_wg0(int genl)
{
    unsigned char p[256];
    size_t len = 0;
    uint16_t port = WG_PORT;
    attr(p, &len, WGDEVICE_A_IFNAME, "wg0", 4);
    attr(p, &len, WGDEVICE_A_PRIVATE_KEY, PRIV, sizeof(PRIV));
    attr(p, &len, WGDEVICE_A_LISTEN_PORT, &port, sizeof(port));
    if (nl_send(genl, wg_family, NLM_F_REQUEST | NLM_F_ACK, WG_CMD_SET_DEVICE, p, len, 1) || nl_receive(genl))
        die("wg_set");
}

static void wg0_up(void)
{
    int s = socket(AF_INET, SOCK_DGRAM, 0);
    if (s < 0) die("flags_socket");
    struct ifreq r;
    memset(&r, 0, sizeof(r));
    strcpy(r.ifr_name, "wg0");
    if (ioctl(s, SIOCGIFFLAGS, &r)) die("get_flags");
    r.ifr_flags |= IFF_UP;
    if (ioctl(s, SIOCSIFFLAGS, &r)) die("set_up");
    close(s);
}

static int drain(int s)
{
    unsigned char buf[2048];
    int cookies = 0;
    for (;;) {
        ssize_t n = recv(s, buf, sizeof(buf), MSG_DONTWAIT);
        if (n < 0) break;
        if (n == 64 && buf[0] == 3 && !buf[1] && !buf[2] && !buf[3]) cookies++;
    }
    return cookies;
}

/* Count cookie replies produced by a burst: settle, then drain, repeatedly,
 * until no more arrive. Caps to avoid an unbounded loop. */
static int harvest(int s)
{
    int total = 0, idle = 0;
    for (int round = 0; round < 200 && idle < 3; round++) {
        usleep(50000);
        int got = drain(s);
        total += got;
        idle = got ? 0 : idle + 1;
        if (total > 100000) break;
    }
    return total;
}

static long send_plain_mmsg(int s, int n)
{
    struct mmsghdr *m = calloc(n, sizeof(*m));
    struct iovec *v = calloc(n, sizeof(*v));
    for (int i = 0; i < n; i++) {
        v[i].iov_base = (void *)INIT;
        v[i].iov_len = SEG;
        m[i].msg_hdr.msg_iov = &v[i];
        m[i].msg_hdr.msg_iovlen = 1;
    }
    long r = syscall(SYS_sendmmsg, s, m, n, 0);
    free(m); free(v);
    return r;
}

/* One sendmsg carrying `segs` GSO segments (UDP_SEGMENT = SEG). */
static long send_gso(int s, int segs)
{
    static unsigned char buf[SEG * GSO_SEGS];
    for (int i = 0; i < segs; i++) memcpy(buf + i * SEG, INIT, SEG);
    int gso = SEG;
    if (setsockopt(s, SOL_UDP, UDP_SEGMENT, &gso, sizeof(gso))) return -1;
    struct iovec v = {.iov_base = buf, .iov_len = (size_t)segs * SEG};
    struct msghdr h = {.msg_iov = &v, .msg_iovlen = 1};
    long r = sendmsg(s, &h, 0);
    gso = 0;
    setsockopt(s, SOL_UDP, UDP_SEGMENT, &gso, sizeof(gso));
    return r;
}

/* sendmmsg of `n` GSO datagrams, each `segs` segments. */
static long send_gso_mmsg(int s, int n, int segs)
{
    static unsigned char buf[SEG * GSO_SEGS];
    for (int i = 0; i < segs; i++) memcpy(buf + i * SEG, INIT, SEG);
    int gso = SEG;
    if (setsockopt(s, SOL_UDP, UDP_SEGMENT, &gso, sizeof(gso))) return -1;
    struct mmsghdr *m = calloc(n, sizeof(*m));
    struct iovec *v = calloc(n, sizeof(*v));
    for (int i = 0; i < n; i++) {
        v[i].iov_base = buf;
        v[i].iov_len = (size_t)segs * SEG;
        m[i].msg_hdr.msg_iov = &v[i];
        m[i].msg_hdr.msg_iovlen = 1;
    }
    long r = syscall(SYS_sendmmsg, s, m, n, 0);
    gso = 0;
    setsockopt(s, SOL_UDP, UDP_SEGMENT, &gso, sizeof(gso));
    free(m); free(v);
    return r;
}

/* Minimal raw io_uring: submit `n` IORING_OP_SEND SQEs in one enter. */
#include <linux/io_uring.h>
static long try_io_uring(int sockfd, int n)
{
    struct io_uring_params pp;
    memset(&pp, 0, sizeof(pp));
    int ring = syscall(SYS_io_uring_setup, n, &pp);
    if (ring < 0) return -1;
    size_t sqsz = pp.sq_off.array + pp.sq_entries * sizeof(unsigned);
    size_t cqsz = pp.cq_off.cqes + pp.cq_entries * sizeof(struct io_uring_cqe);
    void *sq = mmap(0, sqsz, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring, IORING_OFF_SQ_RING);
    void *cq = (pp.features & IORING_FEAT_SINGLE_MMAP) ? sq
             : mmap(0, cqsz, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring, IORING_OFF_CQ_RING);
    struct io_uring_sqe *sqes = mmap(0, pp.sq_entries * sizeof(struct io_uring_sqe),
                                     PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring, IORING_OFF_SQES);
    if (sq == MAP_FAILED || cq == MAP_FAILED || sqes == MAP_FAILED) return -2;
    unsigned *ktail = (unsigned *)((char *)sq + pp.sq_off.tail);
    unsigned *karray = (unsigned *)((char *)sq + pp.sq_off.array);
    unsigned mask = *(unsigned *)((char *)sq + pp.sq_off.ring_mask);
    int submit = n < (int)pp.sq_entries ? n : (int)pp.sq_entries;
    for (int i = 0; i < submit; i++) {
        struct io_uring_sqe *e = &sqes[i];
        memset(e, 0, sizeof(*e));
        e->opcode = IORING_OP_SEND;
        e->fd = sockfd;
        e->addr = (unsigned long)INIT;
        e->len = SEG;
        karray[i & mask] = i;
    }
    __atomic_store_n(ktail, submit, __ATOMIC_RELEASE);
    long r = syscall(SYS_io_uring_enter, ring, submit, 0, 0, 0, 0);
    close(ring);
    (void)cq;
    return r < 0 ? -3 : r;
}

int main(void)
{
    unsigned char seed;
    if (syscall(SYS_getrandom, &seed, 1, 0) != 1) die("getrandom");  /* RNG ready */
    create_wg0();
    int genl = socket(AF_NETLINK, SOCK_RAW, NETLINK_GENERIC);
    if (genl < 0) die("genl_socket");
    resolve_family(genl);
    configure_wg0(genl);
    wg0_up();

    int s = socket(AF_INET, SOCK_DGRAM, 0);
    if (s < 0) die("send_socket");
    struct sockaddr_in src = {.sin_family = AF_INET, .sin_port = htons(SRC_PORT)};
    src.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    if (bind(s, (struct sockaddr *)&src, sizeof(src))) die("bind_src");
    struct sockaddr_in dst = {.sin_family = AF_INET, .sin_port = htons(WG_PORT)};
    dst.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    if (connect(s, (struct sockaddr *)&dst, sizeof(dst))) die("connect_wg0");
    int rcvbuf = 8 << 20;
    setsockopt(s, SOL_SOCKET, SO_RCVBUF, &rcvbuf, sizeof(rcvbuf));

    /* Four burst mechanisms, each after a clean settle (full drain + the 1 s
     * last_under_load decay), reporting the cookie replies it produced. */
    for (int round = 0; round < 4; round++) {
        drain(s);
        sleep(2);              /* full drain + last_under_load (1 s) decay */
        drain(s);
        long sent;
        const char *name;
        switch (round) {
        case 0: name = "gso_sendmmsg"; sent = send_gso_mmsg(s, GSO_DGRAMS, GSO_SEGS); break;
        case 1:
            name = "gso_loop"; sent = 0;
            for (int i = 0; i < GSO_DGRAMS; i++) { long r = send_gso(s, GSO_SEGS); if (r > 0) sent += r; }
            break;
        case 2: name = "plain_sendmmsg"; sent = send_plain_mmsg(s, PLAIN_DGRAMS); break;
        default: name = "io_uring"; sent = try_io_uring(s, PLAIN_DGRAMS); break;
        }
        int cookies = (sent < 0) ? -1 : harvest(s);
        printf("LEANUX_PROBE {\"mechanism\":\"%s\",\"sent\":%ld,\"cookie_replies\":%d,"
               "\"under_load_reached\":%s}\n",
               name, sent, cookies, cookies > 0 ? "true" : (sent < 0 ? "null" : "false"));
        fflush(stdout);
    }
    printf("LEANUX_PROBE_DONE\n");
    fflush(stdout);
    return 0;
}
