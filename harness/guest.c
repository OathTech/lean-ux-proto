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
struct trace { char id[81]; unsigned count; struct operation ops[MAX_OPS]; };
struct observation { long ret; int error; unsigned char bytes[16]; };

static void fail(const char *id, int index, const char *kind, const char *detail)
{
    printf("LEANUX_ERROR {\"id\":\"%s\",\"index\":%d,\"kind\":\"%s\",\"detail\":\"%s\",\"errno\":%d}\n",
           id, index, kind, detail, errno);
    fflush(stdout);
    _exit(1);
}

static int compare_pc(const void *a, const void *b)
{
    unsigned long x = *(const unsigned long *)a, y = *(const unsigned long *)b;
    return (x > y) - (x < y);
}

static long resolve(unsigned kind, long long value, const struct observation *results, unsigned i)
{
    if (!kind) return (long)(int32_t)value;
    if (kind != 1 || value < 0 || (unsigned long long)value >= i) return -1;
    return results[value].ret >= 0 ? results[value].ret : -1;
}

static void execute(const struct trace *t, int input_fd)
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
    struct rlimit limit = {32, 32}, actual;
    if (setrlimit(RLIMIT_NOFILE, &limit) || getrlimit(RLIMIT_NOFILE, &actual) || actual.rlim_cur != 32 || actual.rlim_max != 32)
        fail(t->id, -1, "environment_failure", "rlimit_nofile");
    printf("LEANUX_FIXTURE {\"id\":\"%s\",\"reserved\":[0,1,2,3,4,5,6,7],\"free\":[8,31],\"rlimit\":[32,32]}\n", t->id);
    for (unsigned i = 0; i < t->count; ++i) {
        const struct operation *op = &t->ops[i];
        long fd = resolve(op->kind, op->fd, result, i);
        long newfd = resolve(op->newkind, op->newfd, result, i);
        unsigned char buffer[16];
        memset(buffer, op->code == 5 ? 0xa5 : 0, sizeof(buffer));
        if (op->code == 6)
            for (unsigned j = 0; j < 8; ++j) buffer[j] = (unsigned char)(op->value >> (8 * j));
        if (ioctl(coverage_fd, KCOV_ENABLE, KCOV_TRACE_PC)) fail(t->id, i, "coverage_failure", "enable_kcov");
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
        if (!count || count >= CAPACITY - 1) fail(t->id, i, "coverage_failure", "empty_or_full_kcov");
        result[i].error = ret == -1 ? captured_errno : 0;
        result[i].ret = ret == -1 ? -captured_errno : ret;
        if (op->code == 5 && ret > 0) {
            if (ret > 16) fail(t->id, i, "environment_failure", "read_return_exceeds_buffer");
            memcpy(result[i].bytes, buffer, (size_t)ret);
        }
        /* Deduplication changes coverage representation only, after capture. */
        qsort(coverage + 1, count, sizeof(*coverage), compare_pc);
        printf("LEANUX_COVERAGE {\"id\":\"%s\",\"index\":%u,\"count\":%lu,\"pcs\":[", t->id, i, count);
        int comma = 0;
        for (unsigned long j = 1; j <= count; ++j) {
            if (j > 1 && coverage[j] == coverage[j - 1]) continue;
            printf("%s\"0x%lx\"", comma ? "," : "", coverage[j]);
            comma = 1;
        }
        printf("]}\n");
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
        if (!fgets(line, sizeof(line), input) || sscanf(line, "T %80s %u", trace.id, &trace.count) != 2 || trace.count < 1 || trace.count > MAX_OPS)
            fail("batch", -1, "invalid_input", "wire_trace");
        for (unsigned i = 0; i < trace.count; ++i) {
            struct operation *op = &trace.ops[i];
            if (!fgets(line, sizeof(line), input) || sscanf(line, "%u %u %lld %u %lld %u %u %" SCNu64,
                &op->code, &op->kind, &op->fd, &op->newkind, &op->newfd, &op->a, &op->b, &op->value) != 8)
                fail(trace.id, i, "invalid_input", "wire_operation");
        }
        pid_t child = fork();
        if (child < 0) fail(trace.id, -1, "environment_failure", "fork");
        if (!child) execute(&trace, fileno(input));
        int status;
        if (waitpid(child, &status, 0) != child) fail(trace.id, -1, "environment_failure", "wait_child");
        if (!WIFEXITED(status) || WEXITSTATUS(status)) {
            printf("LEANUX_CHILD_FAILURE {\"id\":\"%s\",\"status\":%d}\n", trace.id, status);
            ++failures;
        }
    }
    if (fgetc(input) != EOF) fail("batch", -1, "invalid_input", "wire_trailing_data");
    fclose(input);
    printf("LEANUX_BATCH_DONE traces=%u failures=%u\n", total, failures);
    return failures ? 1 : 0;
}
