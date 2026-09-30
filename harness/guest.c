/* Linux observations only. Run inside the pinned QEMU guest, never on the host. */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <linux/kcov.h>
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
struct operation { unsigned code, kind, newkind, a, b; long long fd, newfd; uint64_t value; };
struct trace { char id[81]; unsigned count; unsigned rlimit; struct operation ops[MAX_OPS]; };
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
    for (int fd = 4; fd < 8; ++fd)
        if (open("/dev/null", O_RDWR) != fd) fail(t->id, -1, "environment_failure", "fill_descriptor");
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
        default: fail(t->id, i, "invalid_input", "wire_opcode");
        }
        int captured_errno = errno;
        unsigned long count = __atomic_load_n(&coverage[0], __ATOMIC_RELAXED);
        if (ioctl(coverage_fd, KCOV_DISABLE, 0)) fail(t->id, i, "coverage_failure", "disable_kcov");
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
    char line[256];
    unsigned total;
    if (!fgets(line, sizeof(line), input) || strcmp(line, "LEANUX_WIRE_V1\n") ||
        !fgets(line, sizeof(line), input) || sscanf(line, "%u", &total) != 1 || total < 1 || total > 4096)
        fail("batch", -1, "invalid_input", "wire_header");
    struct utsname identity;
    if (uname(&identity)) fail("batch", -1, "environment_failure", "uname");
    printf("LEANUX_KERNEL %s\n", identity.release);
    unsigned failures = 0;
    for (unsigned t = 0; t < total; ++t) {
        struct trace trace;
        if (!fgets(line, sizeof(line), input) || sscanf(line, "T %80s %u %u", trace.id, &trace.count, &trace.rlimit) != 3 || trace.count < 1 || trace.count > MAX_OPS ||
            trace.rlimit < 8 || trace.rlimit > 1024)
            fail("batch", -1, "invalid_input", "wire_trace");
        for (unsigned i = 0; i < trace.count; ++i) {
            struct operation *op = &trace.ops[i];
            if (!fgets(line, sizeof(line), input) || sscanf(line, "%u %u %lld %u %lld %u %u %" SCNu64,
                &op->code, &op->kind, &op->fd, &op->newkind, &op->newfd, &op->a, &op->b, &op->value) != 8)
                fail(trace.id, i, "invalid_input", "wire_operation");
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
