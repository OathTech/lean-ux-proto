# Upstream Linux report drafts: index

> Readers: start with [README.md](README.md), the guide to this directory.

Draft reports against Linux 6.12.110 (`.deps/linux`, the pristine source)
found while mirroring and checking the kernel in this repository. Reports
01 and 02 have corpus evidence on the instrumented single-CPU x86-64 oracle;
03 and 04 are source-analysis questions with no corpus reproducer. The
classifications below are provisional assessments. Filing is the user's call;
no submission is recorded here.

## Submission status

**Draft** = prepared, no recorded submission; **Filed** = reference
recorded; **Withdrawn** = reason recorded in the file.

Recorded inventory: 4 reports, **4 Draft, 0 Filed, 0 Withdrawn**; no
patch branches (README §5).

| Report | Target | Classification | Evidence | State | Drafted |
|---|---|---|---|---|---|
| [01-send-ring-full-drops-uncounted.md](01-send-ring-full-drops-uncounted.md) | `drivers/net/wireguard/send.c`, `queueing.h`; `include/linux/ptr_ring.h` | OBSERVABILITY GAP (the drop: DESIGN NUANCE) | Corpus trace on the oracle | Draft | 2026-10-13 |
| [02-receive-queue-full-drops-uncounted.md](02-receive-queue-full-drops-uncounted.md) | `drivers/net/wireguard/receive.c`, `queueing.h`, `queueing.c` | OBSERVABILITY GAP, with a QUESTION on pre-authentication queueing | Corpus trace on the oracle | Draft | 2026-10-13 |
| [03-index-lookup-stores-null-peer-unlocked.md](03-index-lookup-stores-null-peer-unlocked.md) | `drivers/net/wireguard/peerlookup.c`, `noise.c`, `noise.h` | DESIGN NUANCE, with a QUESTION (a plain store under the RCU read lock into a field read without a check) | Source analysis; no corpus reproducer | Draft | 2026-10-15 |
| [04-staged-packets-stranded-by-racing-flush.md](04-staged-packets-stranded-by-racing-flush.md) | `drivers/net/wireguard/send.c`, `receive.c`, `netlink.c`, `device.c` | DESIGN NUANCE, with a QUESTION (delay, not loss, under a race) | Source analysis; no corpus reproducer | Draft | 2026-10-15 |

## Reading order

Start with 01 and 02 for reproduced observations about uncounted drops.
Read 03 and 04 as questions about races outside this fixture, not as
reproduced failures. Report numbers are stable identifiers, not a severity
ranking; each draft gives its own impact argument and uncertainty.
