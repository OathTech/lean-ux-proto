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
struct operation { unsigned code, kind, newkind, a, b; long long fd, newfd; uint64_t value;
                   unsigned char payload[MAX_PAYLOAD]; size_t payload_len; };
struct trace { char id[81]; unsigned count; unsigned rlimit; unsigned net; struct operation ops[MAX_OPS]; };
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
    if (close(rtnl)) fail(id, -1, "environment_failure", "close_rtnetlink");
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
static void execute(const struct trace *t, int input_fd, int comparisons)
{
    struct observation result[MAX_OPS] = {{0}};
    if (close(input_fd)) fail(t->id, -1, "environment_failure", "close_input");
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
    unsigned long *coverage = mmap(NULL, CAPACITY * sizeof(*coverage), PROT_READ | PROT_WRITE, MAP_SHARED, coverage_fd, 0);
    if (coverage == MAP_FAILED) fail(t->id, -1, "coverage_failure", "map_kcov");
    for (int fd = 4; fd < (t->net ? NETLINK_FD : 8); ++fd)
        if (open("/dev/null", O_RDWR) != fd) fail(t->id, -1, "environment_failure", "fill_descriptor");
    if (t->net) {
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
    for (unsigned i = 0; i < t->count; ++i) {
        const struct operation *op = &t->ops[i];
        long fd = resolve(op->kind, op->fd, result, i);
        long newfd = resolve(op->newkind, op->newfd, result, i);
        unsigned char buffer[16];
        memset(buffer, op->code == 5 ? 0xa5 : 0, sizeof(buffer));
        if (op->code == 6)
            for (unsigned j = 0; j < 8; ++j) buffer[j] = (unsigned char)(op->value >> (8 * j));
        if (ioctl(coverage_fd, KCOV_ENABLE, comparisons ? KCOV_TRACE_CMP : KCOV_TRACE_PC))
            fail(t->id, i, "coverage_failure", "enable_kcov");
        __atomic_store_n(&coverage[0], 0, __ATOMIC_RELAXED);
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
        default: fail(t->id, i, "invalid_input", "wire_opcode");
        }
        int captured_errno = errno;
        unsigned long count = __atomic_load_n(&coverage[0], __ATOMIC_RELAXED);
        if (ioctl(coverage_fd, KCOV_DISABLE, 0)) fail(t->id, i, "coverage_failure", "disable_kcov");
        /* Outside the coverage window: the dump's attribute payloads. */
        if (op->code == 9 && !comparisons && ret == 0)
            printf("LEANUX_WG {\"id\":\"%s\",\"index\":%u,\"payloads\":[%s]}\n", t->id, i, dump_hex);
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
        if (comparisons) {
            /* Records are (type, arg1, arg2, ip). Each distinct record is
             * printed once, at its first occurrence, in execution order. */
            for (unsigned long k = 0; k < count; ++k) {
                memcpy(records[k].record, coverage + 1 + 4 * k, sizeof(records[k].record));
                records[k].position = k;
            }
            qsort(records, count, sizeof(*records), compare_record);
            memset(first, 0, count);
            for (unsigned long k = 0; k < count; ++k)
                if (!k || memcmp(records[k].record, records[k - 1].record, sizeof(records[k].record)))
                    first[records[k].position] = 1;
            printf("LEANUX_CMP {\"id\":\"%s\",\"index\":%u,\"count\":%lu,\"records\":[", t->id, i, count);
            int comma = 0;
            for (unsigned long k = 0; k < count; ++k) {
                if (!first[k]) continue;
                const unsigned long *r = coverage + 1 + 4 * k;
                printf("%s[%lu,\"0x%lx\",\"0x%lx\",\"0x%lx\"]", comma ? "," : "", r[0], r[1], r[2], r[3]);
                comma = 1;
            }
            printf("]}\n");
            continue;
        }
        /* Deduplicate after capture, keeping each PC's first execution in
         * order: sort (pc, position) pairs, mark first positions, then print
         * the marked PCs in execution order. */
        for (unsigned long j = 0; j < count; ++j) {
            order[j].pc = coverage[j + 1];
            order[j].position = j;
        }
        qsort(order, count, sizeof(*order), compare_occurrence);
        memset(first, 0, count);
        for (unsigned long j = 0; j < count; ++j)
            if (!j || order[j].pc != order[j - 1].pc) first[order[j].position] = 1;
        printf("LEANUX_COVERAGE {\"id\":\"%s\",\"index\":%u,\"count\":%lu,\"pcs\":[", t->id, i, count);
        int comma = 0;
        for (unsigned long j = 0; j < count; ++j) {
            if (!first[j]) continue;
            printf("%s\"0x%lx\"", comma ? "," : "", coverage[j + 1]);
            comma = 1;
        }
        printf("]}\n");
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
        _exit(0);
    }
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
    _exit(0);
}

int main(int argc, char **argv)
{
    setvbuf(stdout, NULL, _IOLBF, 0);
    if (argc != 2) fail("batch", -1, "invalid_input", "wire_argument");
    FILE *input = fopen(argv[1], "r");
    if (!input) fail("batch", -1, "environment_failure", "open_wire");
    unsigned total;
    if (!fgets(line, sizeof(line), input) || strcmp(line, "LEANUX_WIRE_V1\n") ||
        !fgets(line, sizeof(line), input) || sscanf(line, "%u", &total) != 1 || total < 1 || total > 4096)
        fail("batch", -1, "invalid_input", "wire_header");
    struct utsname identity;
    if (uname(&identity)) fail("batch", -1, "environment_failure", "uname");
    printf("LEANUX_KERNEL %s\n", identity.release);
    unsigned failures = 0;
    for (unsigned t = 0; t < total; ++t) {
        static struct trace trace;
        if (!fgets(line, sizeof(line), input) || sscanf(line, "T %80s %u %u %u", trace.id, &trace.count, &trace.rlimit, &trace.net) != 4 ||
            trace.count < 1 || trace.count > MAX_OPS || trace.rlimit < 8 || trace.rlimit > 1024 || trace.net > 1)
            fail("batch", -1, "invalid_input", "wire_trace");
        for (unsigned i = 0; i < trace.count; ++i) {
            struct operation *op = &trace.ops[i];
            int consumed = 0;
            if (!fgets(line, sizeof(line), input) || sscanf(line, "%u %u %lld %u %lld %u %u %" SCNu64 "%n",
                &op->code, &op->kind, &op->fd, &op->newkind, &op->newfd, &op->a, &op->b, &op->value, &consumed) != 8)
                fail(trace.id, i, "invalid_input", "wire_operation");
            op->payload_len = 0;
            if (op->code == 8 || op->code == 9) {
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
    printf("LEANUX_BATCH_DONE traces=%u failures=%u\n", total, failures);
    return failures ? 1 : 0;
}
