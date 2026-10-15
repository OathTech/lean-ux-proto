# Upstream Linux report drafts: index

> Readers: start with [README.md](README.md), the guide to this directory.

Draft reports against Linux 6.12.110 (`.deps/linux`, the pristine source)
found while mirroring and checking the kernel in this repository. Every
reproducer ran on the approved oracle build of that source, single-CPU
x86-64 (`kernel/config-x86_64-net-choice`). Filing is the user's call;
nothing here has been submitted.

## Submission status

**Draft** = prepared, no recorded submission; **Filed** = reference
recorded; **Withdrawn** = reason recorded in the file.

Inventory (2026-10-15): 4 reports, **4 Draft, 0 Filed, 0 Withdrawn**; no
patch branches (README §5).

| Report | Target | Classification | State | Drafted |
|---|---|---|---|---|
| [01-send-ring-full-drops-uncounted.md](01-send-ring-full-drops-uncounted.md) | `drivers/net/wireguard/send.c`, `queueing.h`; `include/linux/ptr_ring.h` | OBSERVABILITY GAP (the drop: DESIGN NUANCE) | Draft | 2026-10-13 |
| [02-receive-queue-full-drops-uncounted.md](02-receive-queue-full-drops-uncounted.md) | `drivers/net/wireguard/receive.c`, `queueing.h`, `queueing.c` | OBSERVABILITY GAP, with a QUESTION on pre-authentication queueing | Draft | 2026-10-13 |
| [03-index-lookup-stores-null-peer-unlocked.md](03-index-lookup-stores-null-peer-unlocked.md) | `drivers/net/wireguard/peerlookup.c`, `noise.c`, `noise.h` | DESIGN NUANCE, with a QUESTION (a plain store under the RCU read lock into a field read without a check) | Draft | 2026-10-15 |
| [04-staged-packets-stranded-by-racing-flush.md](04-staged-packets-stranded-by-racing-flush.md) | `drivers/net/wireguard/send.c`, `receive.c`, `netlink.c`, `device.c` | DESIGN NUANCE, with a QUESTION (delay, not loss, under a race) | Draft | 2026-10-15 |

## Ranking [AGENT]

The numbering is the ranking: findings an operator would hit in normal use
first. 01 and 02 describe valid traffic discarded with no statistic; 02
ranks below 01 only because its trigger needs a burst at the receiver
rather than from it. 03 and 04 are questions about behaviour no trace of
this corpus reaches (both need SMP or an interrupt-timed softirq); 04
ranks above 03 because its consequence, a delayed first packet, is one an
operator could meet, where 03's is a benign race under the memory model.
Proposed by the drafting agents for the user to adjust.
