# Independent input and single-CPU interference probe

Baseline `c63423ef`, fresh-eyes review finding 2 and upstream-tray 04.

## Selection fixed before execution

[AGENT 2026-10-21] Take the first 16 candidates returned by
`generate_wireguard(20261021, 16, max_ops=12, steered=.15, data=.15,
timers=.10, alloc=.05, lifecycle=.10, routing=.05, netns=.03)`.
Keep every candidate and every failure; no replacements. The date-derived
seed and count are fixed before running the mirror or Linux. The generator
still embodies its existing fixture grammar, wait budget and deduplication;
this is independence from the mirror's domain verdict, not an unbiased sample
of arbitrary Linux programs or packets.

The emitted JSONL has SHA-256
`563a3c011e9f9dd0ae7f8841d9c5de9fd35b1a0c274de9ef90c1afdb3ca74e48`.

`docs/probe-input-sample.py --emit` reproduces the selection. Its `--run` mode
uses the existing checker's kernel identity, Linux runs, hidden-input replay,
observation, control-flow and operand checks. It substitutes only the loader
and singleton chunking in its own process, and makes a domain-filter call an
error. A singleton per candidate prevents one unsupported case from masking
the remainder of the sample. Syntax/fixture input refusals are reported as
scope findings, not silently removed or counted as agreement.

The selection recipe was committed at `dc4f7457` before its first execution.

## Sample outcome

**PASS: 16/16 traces, 115 operations, 1,592 matched operand pairs and 1,099
distinct operand rows.** Every selected identifier from
`generated-wg-20261021-00000` through `generated-wg-20261021-00015` agreed.
There were zero syntax/fixture refusals, zero unsupported paths, zero mirror
invariant or hidden-record failures, zero filtered/replaced candidates and
zero retries. There are consequently no unsupported cases in this sample
requiring individual classification. This does not estimate the unsupported
rate outside the generator's existing input population.

The run used the approved oracle identity
`b44d958f09743feddc5fdbc3410cb5de89cead4bffdd62b06582b0c560454767`.
The checker's ordinary behavioral, control-flow, operand, instrument and
completion checks were retained. Its report says `status: pass`, with no
aborted run or failures. No harness, evaluator or mirror edits were needed.

From the repository root, after preparing the approved oracle using the
normal build instructions:

```sh
python3 docs/probe-input-sample.py --emit
python3 docs/probe-input-sample.py --run
```

Select a nondefault approved build with `LEANUX_KERNEL_DIR`; on the shared
box prefix the run with `capped -- scripts/in-bundle`. The recipe builds the
native model itself and writes regenerable output under `.artifacts`.

## Single-CPU interference audit of tray 04

Read against the local pristine Linux **6.12.110** source, the approved oracle
configuration, and the current mirror. No SMP execution, kernel alteration or
race reproducer was attempted.

**Established by the source:** one CPU with `CONFIG_PREEMPT_NONE` does not
exclude softirq execution inside a process-context WireGuard call. The UP
`spin_unlock_bh` expansion (`include/linux/spinlock_api_up.h:47-49,79`) reaches
`__local_bh_enable_ip`; on the non-RT path, `kernel/softirq.c:384-415` calls
`do_softirq` when pending work exists and the caller is outside interrupt
context. `rcu_read_unlock_bh` (`include/linux/rcupdate.h:913-920`) also enables
bottom halves. IRQ exit can invoke softirqs (`kernel/softirq.c:652-663`). The
device-update mutex held by netlink callers is not a bottom-half exclusion.

The relevant process-context flush calls are `set_peer` (`netlink.c:482-483`),
the conditional identity-install path (`netlink.c:568-578`), and `wg_open`
(`device.c:50-55`). The first is the least constrained candidate for this
analysis. The other callers have additional lifecycle/identity conditions;
listing them does not prove the required responder state is reachable there.

**Conditional schedule and exact cut:**

1. A process-context flush detaches a nonempty staged queue (`send.c:349-352`).
2. It snapshots an absent or otherwise unusable current key at `:357-360`.
3. Before it puts the detached packets back, a pending RX poll consumes an
   authenticated packet under the responder's pending key, promotes that key
   (`noise.c:253-291`), and invokes
   the confirmation flush (`receive.c:345-349`). That flush sees the shared
   staged queue empty and returns. A concrete candidate cut is the **second**
   BH-enable, `rcu_read_unlock_bh` at `send.c:360`, after the key snapshot.
4. The interrupted flush resumes with its saved unusable key, takes
   `out_nokey`, and restores the packets at `send.c:406-408`. It does not
   reload the now-current key before returning.

Tray 04's suggestion that the first unlock (`send.c:352`) alone suffices is
too broad. If confirmation finishes there and supplies a valid current key,
the interrupted caller subsequently reads that new key and can send its local
packets. The second cut preserves the stale key decision; the first does not.
This distinction also matters to the mirror: `Send.sendStagedPackets` retains
the initial peer value and has no scheduler callback between queue detach,
key selection and put-back. Its atomic treatment needs an explicit environment
restriction, not merely the label “single CPU.”

**Unresolved reachability obligation:** an incoming transport datagram is not
yet a confirmation. `receive.c:495-510` decrypts in a workqueue, publishes the
result and schedules NAPI (`queueing.h:193-203`); `receive.c:439-478` requires a
crypted packet and validates its replay counter before the confirmation call.
On a nonpreemptible single CPU, a fresh wire arrival during the narrow flush
interval does not by itself run that decrypt worker. The proposed interference
therefore needs suitable already-decrypted RX work pending at the critical
cut, and an explanation why earlier BH-enable points did not consume it.
The source permits budget-limited pending softirq work (`softirq.c:537-609`),
but this audit has not constructed an initialized UP schedule meeting all
those conditions. A physical race on the configured oracle remains **unproved**.

The fixture and mirror do not test this contract: their NAPI placements are
the explicit `Env.Batch.napiSoftirq` / `napiIrqExit` worker cuts, and they refuse
multiple peers' NAPI polls in one softirq. This is a scope finding about an
unverified environment exclusion, not evidence that general UP execution is
covered or that the mirror has accepted this racing execution.

The claimed indefinite delay also needs qualifications. The confirming
keepalive skips `wg_timers_data_received` (`receive.c:355-365`), but authenticated
traversal arms persistent keepalive when configured (`timers.c:212-217`). Other
existing timers or later sends can provide a trigger. Suppression of the queued
initiation relies on the actual last-handshake time and `REKEY_TIMEOUT`
(`send.c:21-27,63-67`). The conditional delay case needs those alternate
triggers absent or delayed. This audit establishes no time bound, attacker
control, packet-loss claim or invalid-memory-access claim.

**Disposition:** retain tray 04 as a design question with no reproducer;
correct the first-unlock interpretation and make the unresolved UP schedule
and fixture restriction explicit. Do not promote it to a demonstrated kernel
bug, and do not broaden this probe into an SMP campaign.
