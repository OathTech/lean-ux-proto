# Steering hidden inputs — design, 2026-10-03

Status: **proposed** [AGENT], revised after a critical audit (section 10).
Its kernel mechanism (sections 4.2, 7.2) is superseded by the
[choice-stream strategy](2026-10-03-choice-stream-strategy.md) [USER
direction 2026-10-03]; its semantics (complete schedules, supplied values
still recorded, the exact check, expected outcomes) and the D1 scope stand. It builds on the
[hidden-inputs design](2026-10-03-hidden-inputs-design.md), which is merged.

## 1. Two questions

The user separated two questions on 2026-10-03 [USER]:

1. **Correspondence.** Given the inputs Linux actually consumed, including
   hidden ones, does the mirror do what Linux does in data and control flow?
   This is where the rigor goes. The recording instrument answers it: the
   mirror consumes the values Linux recorded, and is checked step by step.
2. **Input selection.** Which executions do we probe? They need not be
   realistic deployments. "This is about randomized probing not necessarily
   completely realistic executions of linux for test data." Frozen test
   vectors and odd configurations are fine, as long as each is an input the
   real code can genuinely receive.

Recording serves question 1. This design adds **steering** for question 2: a
trace may choose the values of hidden inputs, instead of taking the kernel's
draws. Steering must never weaken question 1 (section 5).

## 2. Why steering

The WireGuard initiator role needs the test to answer wg0's initiation. The
response depends on three values in wg0's initiation:
- the random ephemeral key;
- the random sender index;
- the timestamp. Its ciphertext enters the hash chain, which is the AAD of
  the response's `encrypted_nothing`.

With drawn values, a valid response must be computed live. With steered
values, `harness/noise.py` computes it offline, and the trace stays frozen
and batch-run.

Steering also reaches states that drawn values almost never produce:
- **An index collision.** It exercises the retry in
  `wg_index_hashtable_insert`.
- **A message naming a live index.** It exercises lookups that find an
  entry.

## 3. The semantic rule

A site is **steerable** only if both hold:
- every value in its declared domain is a possible output of the source;
- the value does not interact with any other hidden input that is not
  steered.

Each site declares its domain; values are validated once, when the
schedule is loaded.

| Site | Source | Domain | Steerable |
|---|---|---|---|
| `noise.c:541`, `:688` | `curve25519_generate_secret`: 32 random bytes, then clamp (`curve25519.h:61-71`); the hook follows the clamp | clamped 32-byte values. The clamp's image is exactly its fixed points, so a substituted clamped value equals some draw followed by the real clamp. With a clamped secret, `curve25519_generate_public` cannot fail (`noise.c:543-544` stays unreachable). | yes |
| `peerlookup.c:132` | `get_random_u32` | all of `u32`. A retry after a collision is a second, independent draw. | yes |
| `noise.c:501` | `ktime_get_real_ts64` in `tai64n_now` | `0 ≤ tv_sec < TIME_SETTOD_SEC_MAX`, `0 ≤ tv_nsec < 10^9` (`time64.h:44,113-121`) | yes |
| `timers.c:197` | `ktime_get_real_ts64` into `walltime_last_handshake` | same | **record only**: nothing needs it steered (the dump compares the recorded value) |
| every other clock read | coarse boot time, jiffies | — | no: they are compared with each other |

Two notes on `tai64n_now`:
- **Who compares the timestamp.** wg0 never compares its own timestamp:
  `latest_timestamp` is updated only from peers' initiations
  (`noise.c:636-650`). A remote responder's replay check does compare it.
  For a real peer, a non-increasing stamp is still a legitimate execution,
  because the wall clock can be set.
- **Rounding.** The hook precedes `ALIGN_DOWN` (`noise.c:507-508`). So
  `noise.response`, the mirror and the domain filter all round the steered
  nanoseconds the same way.

## 4. Mechanism

### 4.1 A steering schedule, not a value list

A steered trace carries a complete **schedule** of the hooked sites' hook
encounters in that trace, in order. Each entry is either `[site, value]` or
`[site, "draw"]` ("take the kernel's draw").

The schedule is exactly the sequence of hidden-input reads the mirror
predicts. So:
- every encounter is accounted for;
- a site mismatch is always a path deviation, and fails noisily;
- both guest children take the same path.

A trace without a schedule behaves as today: every encounter draws.

Partial schedules ("steer the first k encounters") are not allowed. The
generator produces schedules by running the mirror with placeholders to
predict the encounters (section 6.3).

### 4.2 Per-handle queue, loaded by ioctl, consulted only inside sections

The schedule is attached to the trace's KCOV remote handle:
- **Where it lives:** a queue in the `kcov_remote` entry for the common
  handle (`kcov.c:81-85`, found by `kcov_remote_find`). That entry exists
  exactly while the guest's parent holds `KCOV_REMOTE_ENABLE`
  (`guest.c:474`).
- **Loading:** a new ioctl on that fd, before the fork that starts the trace
  process (`guest.c:475`). No debugfs file and no change to the child's fd
  layout. The guest's process tree is `main` → run child → the
  `enable_remote` parent → the trace process; one schedule is loaded per
  trace process, and there is one per guest child.
- **Reading back:** after `waitpid` (`guest.c:479`), the parent reads the
  queue's remaining length through the same fd. Anything left fails the
  trace (`steering_unconsumed`).

The hooks find the queue through the device, which already holds the
handle:
- `handshake->entry.peer->device->kcov_handle`;
- `entry->peer->device`;
- `peer->device`.

They consult it **only when the current context records**: the same
`check_kcov_mode` test as recording. So steering happens exactly where the
value is recorded. Outside any KCOV context nothing is steered and nothing
recorded. That rules out:
- the retransmit timer (`timers.c:184-186`, 5 s plus jitter, beyond the
  trace bound), which can run the send worker after the trace ends;
- softirq callers without a section, such as `wg_packet_rx_poll`'s
  `wg_timers_handshake_complete`, `receive.c:347`.

Neither can consume another run's schedule.

A queue access takes the remote lock. A mismatch (the head names another
site) writes a marker into the active stream, which exists because the
context records. The guest then fails the trace (`steering_mismatch`).

### 4.3 Records carry the steered flag

Each record's header word gains a steered bit (16 bits are free in both
layouts). `split_hidden`, `hidden.jsonl` and `HiddenRecord` carry it.

## 5. Keeping question 1 intact

The mirror still consumes records, not the schedule. Steering adds checks;
it removes none.

1. **Exact schedule check, per child.** The sequence of records (task
   stream, then remote, across operations) must match the schedule entry
   for entry:
   - each `[site, value]` matches a record of that site, flagged steered,
     with that value;
   - each `draw` matches a record of that site, flagged drawn;
   - there are no extras.

   This catches a hook that substitutes nothing, substitutes at the wrong
   point, or matches an encounter early.
2. **Expected outcome, asserted against Linux.** A steered trace states
   what its steering is for: for D1, a 32-byte keepalive with the expected
   `key_idx` in `wg_observe`'s replies, and `last_handshake` set in the
   dump. The check asserts it against Linux's observation. Otherwise a
   steering bug that leaves Linux and the mirror agreeing on a failed
   handshake would pass silently.
3. **Domain prediction.** For a steered trace, the domain filter's
   predicted decision sequence (run on the schedule) must equal the
   authoritative run's.

## 6. The first consumer: the WireGuard initiator role (stage D1)

### 6.1 The trace

1. **Configure.** wg0 gets a private key and one peer: a public key whose
   private key the trace knows, an endpoint at the fixture's listener, a
   persistent keepalive of 25 s (beyond the trace bound), and optionally a
   PSK.
2. **Bring wg0 up** (`wg_up`). `wg_open` stages a zero-length keepalive
   (`device.c:54-58`). The send worker creates an initiation from the
   steered ephemeral, timestamp and index.
3. **Inject the response** from the fixture's sender. `noise.response(...)`
   computed it offline, from the steered values and the peer's keys. Its
   receiver index is wg0's steered index.
4. **wg0 consumes the response.** It runs `consume_response`, begins the
   session as initiator, and sends the staged keepalive through the encrypt
   and tx workers. The endpoint is learned from the response first
   (`receive.c:172-176`).
5. **`wg_observe`** shows the keepalive's 32 bytes at the sender, and the
   dump shows the recorded `last_handshake`.

A `wg_xmit` trigger is out of scope. It stages a data packet whose payload
carries an IP ident chosen below the cut. Data packets also reach the
unhooked jitter draw (`timers.c:150`, via `data_sent`).

### 6.2 Target traces beyond the basic one

- **Tampered responses:** a flipped `encrypted_nothing`, and a wrong
  receiver index (a lookup miss).
- **A second response after the session.** The state is no longer
  `CREATED_INITIATION`.
- **Respond, then initiate, within 4 s.** wg0 first answers an injected
  initiation, giving it a pending next keypair, then initiates. This
  exercises the initiator arm's demotion of the next keypair
  (`noise.c:211-222`).
- **An index collision with a live partner.** Two peers, both handshakes
  steered. The second insert's first draw equals the first peer's live
  index, then the second draw is fresh. The partner's index is steered too.
  The "stolen" recheck (`peerlookup.c:144-153`) is unreachable on one CPU
  and stays `unsupported`.
- **A lookup that finds an entry.** A cookie message and a data message
  naming a steered live index. Both arms are then `unsupported` beyond the
  lookup, which is now reached.

### 6.3 The generator

1. Generate the configuration and operations.
2. Run the mirror with placeholders to predict the hook encounters in order.
3. Assign each encounter a value (random within its domain, or a deliberate
   collision) or `draw`.
4. Compute any response with `noise.response`, which needs wg0's steered
   index, the public of the steered ephemeral, `h` from the rounded steered
   timestamp, and MAC1 keyed by BLAKE2s("mac1----" ‖ wg0's public).
5. Insert the `wg_inject`.
6. Re-run the domain filter on the final trace.

## 7. The initiator path in the C

This section comes from a read-only mapping of
`.deps/linux/drivers/net/wireguard`, corrected by the audit. Line numbers are
in the unpatched source.

**Contexts, in order on one CPU with `PREEMPT_NONE`.** The receive worker
yields only at `cond_resched` (`receive.c:216`), after its per-skb epilogue.
`wg-kex` (receive) and `wg-crypt` are per-CPU pools; only `handshake_send_wq`
is unbound. The order B → C → D below is assumed today; section 7.3 makes it
checked.

- **A, softirq in the trace's `sendto`.** `wg_receive` queues the response.
  This is mirrored already.
- **B, the handshake receive worker.** `wg_receive_handshake_packet`'s
  response arm (`receive.c:157-188`) calls `wg_noise_handshake_consume_response`
  (`noise.c:727-814`), which does:
  - `has_identity`;
  - the index lookup, with mask `HANDSHAKE`;
  - `state == CREATED_INITIATION`;
  - `message_ephemeral` (copy);
  - two `mix_dh` calls with a NULL key: `ee` from wg0's recorded or steered
    ephemeral, `se` from its static;
  - `mix_psk`;
  - `message_decrypt` of `encrypted_nothing`;
  - the state recheck;
  - the writes, including `remote_index` = the response's sender index.

  Then:
  - the endpoint is learned from the skb;
  - `begin_session`'s initiator arm runs: `derive_keys(sending, receiving)`;
    `add_new_keypair`'s initiator arm, which demotes a pending next
    keypair; `current = new`; the index replace;
  - `wg_timers_session_derived`;
  - `wg_timers_handshake_complete`, with the record-only wall-clock read;
  - `wg_packet_send_keepalive`, which reuses the keepalive staged at
    `wg_up`;
  - `wg_packet_send_staged_packets` with a current keypair: get, validity,
    birthdate, nonce 0;
  - `wg_packet_create_data`, which enqueues, chooses a CPU, and queues
    work;
  - the receive epilogue.
- **C, the encrypt worker** (`send.c:287-309`): `encrypt_packet` (no padding
  for a zero-length payload with MTU 1420; ChaCha20-Poly1305 under the
  sending key with nonce 0), `wg_reset_packet`, the per-peer tx enqueue
  (the first-use branch of `serial_work_cpu`).
- **D, the tx worker** (`send.c:262-285`): `create_data_done`,
  `wg_socket_send_skb_to_peer`, `keep_key_fresh`, and the keypair and peer
  puts (`send.c:280-281`, decisions the mirror reports).

### 7.1 The keepalive's bytes

`le32 4 ‖ le32 key_idx ‖ le64 0 ‖ tag`:
- `key_idx` is the response's sender index (`send.c:207`);
- the tag is the AEAD of the empty string under the first output of
  `kdf(ck_final, "")`, with nonce 0;
- every input is in the mirror.

### 7.2 Sections

- **The encrypt worker:** a section around each ring item.
- **The tx worker:** a section around each invocation, enclosing the loop
  and its puts.

Both are opened with the device-held handle, on existing lines. The device
handle is used for uniformity, not because the skb's handle is missing: the
keepalive staged at `wg_up` was allocated by the trace process and carries
its handle, but a keepalive allocated in the receive worker carries 0.

Encrypt and tx are separate work items, so no section nests in another. A
nested `kcov_remote_start` warns and returns (`kcov.c:871`), and the inner
stop would close the outer section (`kcov.c:1010`).

`flush_workqueue(packet_crypt_wq)` in peer removal (`peer.c:116-118`) blocks
the netlink task while a kworker runs the pending crypt items. Their
sections land in that operation's remote stream, and the mirror runs them
there.

### 7.3 Section records (required)

Each section start records a "section" entry naming the worker (send,
receive, encrypt, tx). Consumed in order, these entries make the worker
order checked rather than assumed. They are the first schedule records the
hidden-inputs design anticipated (section 6 there).

### 7.4 State the mirror needs

- **A keypair store** (`current` / `previous` / `next`; each keypair's
  keys, counters, validity, role, refcount, remote index), replacing the
  `nextKeypair` flag.
- **Staged packets** as a list of lengths.
- **The CPU choices:** `encrypt_queue.last_cpu` and `serial_work_cpu`.
- **The crypt and tx queues**, with packet states.
- **`walltime_last_handshake`.** The dump stops hard-coding `[0,0]`
  (`Netlink.lean:341`).

`keypairs_clear` and `expire_current_peer_keypairs` with a current keypair
are mirrored, not excluded.

### 7.5 Unsupported (fail-noisy) in D1

- staged payload packets meeting a session;
- any received data message naming a keypair (the decrypt path);
- more than one item in a crypt queue;
- cookies under load;
- rekey and expiry timers;
- `wg_prev_queue`'s MPSC internals (`queueing.c` is unanchored, so they are
  mirrored as "the queue yields the packet");
- `encrypt_packet`'s skb surgery, which is cut with its failure branches
  under `envOk`.

### 7.6 Plumbing

- **Trace format.** `harness/trace.py` (`validate_trace`, the wire format's
  header) gains `steer`.
- **Guest.** It loads the schedule by ioctl, splits the steered flag, and
  reads back the leftover count.
- **Harness.** `harness/linux.py`'s hidden rows gain the flag.
- **Mirror and runner.** `HiddenRecord` gains the flag, and the placeholder
  path takes `trace.steer`.
- **Evaluator.** `evaluator/check.py` adds the checks of section 5.

## 8. Decisions for the user

1. **The steering mechanism and its rule** (sections 3–5):
   - a complete schedule per trace, attached to the trace's KCOV handle and
     consulted only in recording contexts;
   - steerable sites: the two ephemerals, the index draw, and `tai64n_now`'s
     clock read, which has the bounded domain;
   - `walltime_last_handshake` recorded only.
2. **The kernel patch change.** The steering ioctl, the new record hook,
   the encrypt and tx sections, and the section records. It replaces the
   oracle once checked.
3. **The stage D1 scope** (sections 6–7), including what stays
   `unsupported`.

## 9. What would show steering pays for itself

- **Coverage recording alone cannot reach:**
  - `consume_response`, the initiator session, and the keepalive bytes;
  - the collision retry;
  - lookups that find an entry.

  Each would be shown with traces and coverage.
- **Mutants:**
  - **Kernel:** steering before the clamp. Only the exact schedule check
    (section 5.1) catches it.
  - **Mirror:**
    - initiator keys derived in responder order (`noise.c:832-837`);
    - the wrong index in `key_idx`.

    Only the keepalive bytes catch these two.
  - **Mirror:** skipping the demotion of the pending next keypair. This
    needs the respond-then-initiate trace.
- **Negative controls:**
  - a schedule with a wrong site;
  - a schedule with an extra entry;
  - a schedule with a missing entry;
  - a steered trace whose expected outcome is withheld by tampering.

  Each must fail noisily.

## 10. Audit [AGENT 2026-10-03]

An independent Fable audit of the first version found three blocking
defects:
- **The schedule was undefined.** "Head must match" made steering
  all-or-nothing without saying so. Now it is a complete schedule
  (section 4.1).
- **A silent failure.** A same-site encounter could consume an entry early
  while the check passed. Now there is an exact schedule check and an
  expected outcome (section 5).
- **The scope was wrong.** A global debugfs queue could leak into the next
  run through the retransmit timer at 5 s, be consumed by softirq callers
  without a section, and had no stream for mismatch markers. Now it is a
  per-handle queue, loaded by ioctl and consulted only in recording
  contexts (section 4.2).

It also found serious issues:
- the clock domain was too wide;
- `walltime_last_handshake` did not need steering;
- `tai64n`'s rounding and replay caveats were missing;
- an index collision needs a live partner;
- the skb-handle claim was wrong;
- the section placement was ambiguous;
- the worker order should be checked;
- mutants were missing.

And minor issues: plumbing, the generator loop, and validation stated twice.

All are addressed above. It confirmed:
- the clamp argument and the `u32` domain;
- that a zero-length keepalive is staged at `wg_up`;
- the keepalive byte layout;
- the `consume_response` summary;
- the yield points.
