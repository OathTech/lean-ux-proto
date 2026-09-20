/* Dependency/guest smoke test, not the differential oracle implementation. */
#include <errno.h>
#include <fcntl.h>
#include <linux/kcov.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/eventfd.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/utsname.h>
#include <unistd.h>

static void require(int condition, const char *operation)
{
    if (!condition) {
        fprintf(stderr, "LEANUX_SMOKE_FAIL %s errno=%d\n", operation, errno);
        exit(1);
    }
}

int main(void)
{
    const unsigned long capacity = 64 * 1024;
    int coverage_fd = open("/sys/kernel/debug/kcov", O_RDWR);
    require(coverage_fd >= 0, "open kcov");
    require(ioctl(coverage_fd, KCOV_INIT_TRACE, capacity) == 0, "initialize kcov");
    unsigned long *coverage = mmap(NULL, capacity * sizeof(*coverage),
                                  PROT_READ | PROT_WRITE, MAP_SHARED, coverage_fd, 0);
    require(coverage != MAP_FAILED, "map kcov");
    require(ioctl(coverage_fd, KCOV_ENABLE, KCOV_TRACE_PC) == 0, "enable kcov");
    __atomic_store_n(&coverage[0], 0, __ATOMIC_RELAXED);

    int original = eventfd(0, EFD_NONBLOCK | EFD_CLOEXEC);
    require(original >= 0, "eventfd");
    int alias = dup(original);
    require(alias >= 0, "dup");
    require(fcntl(original, F_GETFD) == FD_CLOEXEC, "original descriptor flags");
    require(fcntl(alias, F_GETFD) == 0, "duplicate descriptor flags");
    uint64_t value = 5;
    require(write(original, &value, sizeof(value)) == sizeof(value), "write");
    require(close(original) == 0, "close original");
    value = 0;
    require(read(alias, &value, sizeof(value)) == sizeof(value) && value == 5,
            "read shared counter after closing original");
    require(read(alias, &value, sizeof(value)) == -1 && errno == EAGAIN,
            "nonblocking empty counter");
    require(close(alias) == 0, "close alias");

    unsigned long count = __atomic_load_n(&coverage[0], __ATOMIC_RELAXED);
    require(ioctl(coverage_fd, KCOV_DISABLE, 0) == 0, "disable kcov");
    require(count > 0 && count < capacity, "nonempty untruncated coverage");
    struct utsname identity;
    require(uname(&identity) == 0, "uname");
    printf("LEANUX_KCOV_SMOKE_PASS value=5 pcs=%lu kernel=%s\n", count, identity.release);
    for (unsigned long i = 0; i < count; ++i)
        printf("KCOV_PC=0x%lx\n", coverage[i + 1]);
    require(munmap(coverage, capacity * sizeof(*coverage)) == 0, "unmap kcov");
    require(close(coverage_fd) == 0, "close kcov");
    return 0;
}
