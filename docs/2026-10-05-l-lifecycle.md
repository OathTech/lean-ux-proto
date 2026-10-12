# L: WireGuard device lifecycle — design, 2026-10-05

**Decisions [USER 2026-10-06, "These all seem fine, approved"]:** the trust-surface and scope items — A1 (steer atomic-class allocations first; task-context forced failures as a separately decided failslab-style extension), A3 (custom mm hooks, oracle change signed off at the end), A5 (phased rollout; the transitional unarmed fail-open declared and removed by plan), E18 (flood coverage-only, ratelimiter stretch), E19 (section-discard primitive with the two-section fail-closed assertion), P9 (mirror kernel/signal.c to the pending set), L12 (lifecycle scope; netns exit deferred). The remaining (operational) items follow the recommendations in the design as [AGENT] decisions, delegated by the user.

Status: **proposed** [AGENT], revised after an independent audit (section
15), for the user's decisions in section 13. The direction is the user's
[USER 2026-10-04]: complete coverage of WireGuard's single-CPU behaviour. L covers what happens to `wg0` *as a device*: creation
inside a trace, going down and up again, changing the listen port while up,
and deletion inside a trace. Today every trace starts with a down `wg0`
created by the fixture before the window, goes up at most once, never changes
its port while up, and is deleted after the window (choice-stream strategy,
section 4.4). Line numbers are in the unpatched `.deps/linux` (6.12.110);
the kernel is `kernel/config-x86_64-net-choice`: one CPU, `PREEMPT_NONE`,
`TINY_RCU` (`:130`), `NET_NS=y` (`:161`), no `USER_NS` (`:159`), no `PM` or
`SUSPEND` (`:372-373`), no `MODULES` (`:550`), no `IP_MULTICAST` (`:686`),
`IPV6_SIT=y` (`:720`), no `UEVENT_HELPER` (`:814`), no `ACPI` (`:375`), no
`VMGENID` (absent from the config; it depends on `ACPI`).

L needs **no kernel change**. It adds three fixture operations, one trace
field, mirror functions for `device.c`'s remaining paths, environment rules
for what the fixture's routes and sockets do, and seven new choice sites
(five mirror, one computed mirror site for the random port, and one cut
consumer that records twice per creation).

## 1. Target

Every path of `drivers/net/wireguard/device.c` reachable on one CPU, checked
against Linux, plus the running-device arms of `netlink.c`'s `set_port` and
`socket.c`'s `wg_socket_init`/`wg_socket_reinit`:

| # | Scope item | C entry | Observable through |
|---|---|---|---|
| 1 | create `wg0` in a trace | `RTM_NEWLINK` → `rtnl_newlink_create` (`rtnetlink.c:3581-3671`) → `wg_setup` (`device.c:274-307`), `wg_newlink` (`:309-400`), `register_netdevice` (`dev.c:10511`) | the ACK's error code; `wg_get` works (`ENODEV` before); the dump's `ifindex`; later behaviour |
| 2 | down, then up again | `SIOCSIFFLAGS` → `dev_change_flags` (`dev.c:9032-9045`) → `__dev_close` → `wg_stop` (`device.c:115-135`); then `__dev_open` → `wg_open` (`:31-62`) with existing peers | `tx_dropped` (purged staged packets); the dump (keypairs gone, `last_handshake` kept, port kept); initiations and keepalives at the second open; `wg_xmit` fails with `ENETUNREACH` while down (the routes are gone) |
| 3 | listen port on a running device; fwmark while up | `set_port` (`netlink.c:314-327`) → `wg_socket_init` (`socket.c:349-417`), `wg_socket_reinit` (`:419-437`) | the ACK (`0` or `-EADDRINUSE`); the dump's `listen_port`; the source port of wg0's datagrams at the sender; a random port when the port is 0 |
| 4 | delete `wg0` in a trace | `RTM_DELLINK` → `rtnl_dellink` (`rtnetlink.c:3383-3436`) → `unregister_netdevice_many_notify` (`dev.c:11493`) → `wg_stop` if up → `netdev_run_todo` (`:10890-10954`) → `wg_destruct` (`device.c:242-270`) | the ACK; `ENODEV` from `wg_get`/`wg_set`/`wg_up` afterwards; `stats: null` from `wg_observe`; the ratelimiter's global state (E) |
| 5 | netns exit, PM and VM notifiers | `wg_netns_pre_exit` (`device.c:409-428`), `wg_pm_notification` (`:64-95`), `wg_vm_notification` (`:97-113`) | **out of scope**, with reasons (section 10) |
| 6 | module init and exit | `wg_mod_init` (`main.c:20-61`), `wg_mod_exit` (`:63-69`) | **declared cuts**: built in, run at boot, before any window (section 2.6) |

## 2. The kernel paths, verified

### 2.1 Creating wg0: `RTM_NEWLINK`

The guest's fixture already issues this message (`harness/guest.c:174-197`,
`network_fixture`): `IFLA_IFNAME` "wg0", `IFLA_LINKINFO/IFLA_INFO_KIND`
"wireguard", flags `NLM_F_CREATE|NLM_F_EXCL|NLM_F_ACK`, `ifi_index` 0,
`ifi_flags` 0. Inside the trace process's `send()`: `netlink_unicast` runs
`rtnetlink_rcv` synchronously, which is `netlink_rcv_skb(skb,
&rtnetlink_rcv_msg)` (`rtnetlink.c:6784-6787`); `rtnetlink_rcv_msg` takes
and releases `rtnl` around each message's handler, and `netlink_rcv_skb`
queues the ACK after the handler returns. So the whole creation — and, for
`RTM_DELLINK`, the `netdev_run_todo` that the handler's `rtnl_unlock` runs —
completes before the ACK is queued and before `send()` returns; the
following `recv()` reads the ACK.

1. **The core** (`rtnetlink.c`): `__rtnl_newlink` looks the name up
   (`:3716-3718`); an existing device with `NLM_F_EXCL` is `-EEXIST`
   (`:3787-3791`) and no WireGuard code runs. Otherwise `rtnl_newlink_create`
   (`:3581-3671`): `rtnl_create_link` → `alloc_netdev_mqs(priv_size, "wg0",
   NET_NAME_USER, wg_setup, 1, 1)` (`:3499-3501`), `dev_net_set`,
   `rtnl_link_state = INITIALIZING` (`:3513-3515`); `dev->ifindex =
   ifm->ifi_index` = 0 (`:3632`); `ops->newlink` (`:3634-3635`);
   `rtnl_configure_link` (`:3643`, `:3438-3459`: `ifi_flags` 0, so no
   `__dev_change_flags`; the state becomes `INITIALIZED` and `RTM_NEWLINK`
   is broadcast to no listener).
2. **`wg_setup`** (`device.c:274-307`): ops, `ARPHRD_NONE`,
   `IFF_POINTOPOINT|IFF_NOARP` (`:290`), `IFF_NO_QUEUE`, `mtu = 1500 − 80`
   (`:296`; the mirror's `DEVICE_MTU`), `memset(wg, 0)` (`:305`).
3. **`wg_newlink`** (`device.c:309-400`), in order:
   - `creating_net = src_net` (`:316`), locks, `wg_allowedips_init`
     (`:320`; `allowedips.c:252-256`: roots NULL, `seq = 1`),
     **`wg_cookie_checker_init`** (`:321`; `cookie.c:19-26`: `secret_birthdate
     = ktime_get_coarse_boottime_ns()` at `:23`, `get_random_bytes(secret, 32)`
     at `:24`), `device_update_gen = 1` (`:323`);
   - **`wg_pubkey_hashtable_alloc`** (`:325`; `peerlookup.c:22-33`:
     `kvmalloc`, `get_random_bytes(&table->key, 16)` at `:29`);
   - `wg_index_hashtable_alloc` (`:329`; `peerlookup.c:84-93`, no draw);
   - three `alloc_workqueue`s (`:333-346`): `handshake_receive_wq`
     (`WQ_CPU_INTENSIVE|WQ_FREEZABLE`), `handshake_send_wq`
     (`WQ_UNBOUND|WQ_FREEZABLE`), `packet_crypt_wq`
     (`WQ_CPU_INTENSIVE|WQ_MEM_RECLAIM`). Only the last gets a rescuer kthread
     (`workqueue.c:5603-5635`: `init_rescuer` returns at once without
     `WQ_MEM_RECLAIM`, `:5611`; `kthread_create` at `:5624`). The unbound
     one reuses the existing default-attribute pool (`get_unbound_pool`,
     `:5043-5056`: a hash hit increments `refcnt`; a worker is created only
     for a new pool, `:5081`). The kthread is created by `kthreadd`, not by
     the trace process, so its `copy_process` clock reads are outside every
     recording context (records are written only when `current` has KCOV
     enabled). The trace process **sleeps** in `kthread_create`'s
     completion wait: a `mayHaveSlept` point (section 5);
   - three `wg_packet_queue_init`s (`:348-361`; `queueing.c:25-41`:
     `ptr_ring_init`, `alloc_percpu`, `last_cpu = -1`);
   - **`wg_ratelimiter_init`** (`:363`; `ratelimiter.c:158-203`): a global,
     refcounted singleton (the statics at `:12-18`). Only when
     `++init_refcnt == 1` (`:161`) does it create the slab cache
     (`:164-165`), size the tables from RAM (`:173-177`; 2048 buckets for
     the 256 MB guest), allocate them (`:179-185`), queue the GC on
     `system_power_efficient_wq` every `HZ` (`:191`) and **draw the 16-byte
     hsiphash key** (`:192`). A failed allocation undoes the increment
     (`:200`). The fixture creates and deletes one device per trace, so the
     count is 0 at every trace start **provided every trace process ran its
     teardown** (section 2.4, the failure path), and the first creation in a
     trace draws;
   - `register_netdevice` (`:367`): the ifindex (`dev.c:10000-10018`:
     `xa_alloc_cyclic` on `net->dev_by_index`, `:10009-10011`, initialised
     `XA_FLAGS_ALLOC1` at `:12012`, so index 0 is busy (`xarray.h:274,282`)
     and the first device is 1; `net->ifindex` is the cyclic cursor and is
     never reset). In the fixture netns `lo` is 1, `sit0` is 2
     (`IPV6_SIT=y`), so the first `wg0` is **3**, as the harness assumes
     (`guest.c:45`), and a `wg0` recreated after a deletion is **4**. Then
     `NETDEV_REGISTER`: `inetdev_event` → `inetdev_init` (`devinet.c:1576-1580`,
     `:277-295`) → **`neigh_parms_alloc(dev, &arp_tbl)`** (`:291`), and
     `addrconf_notify` → `ipv6_add_dev` (`addrconf.c:3683-3688`; the MTU
     1420 ≥ 1280) → **`neigh_parms_alloc(dev, &nd_tbl)`** (`:399`). Each
     `neigh_parms_alloc` (`neighbour.c:1716-1730`) sets `reachable_time =
     neigh_rand_reach_time(BASE_REACHABLE_TIME)` (`:1727-1728`), an exported
     out-of-line function (`:113-117`) that calls `get_random_u32_below(base)`
     with a non-constant ceiling: **two `__get_random_u32_below` records**
     at consumer frame `neigh_rand_reach_time` (`neighbour.c:115`). The value
     reaches only the neighbour tables of a `NOARP` point-to-point device that
     no modeled path consults: a **cut consumer** of the `wg_create` cut
     point. The sysfs/kobject registration broadcasts a uevent to no listener
     and runs no helper (`UEVENT_HELPER` unset; `kobject_uevent.c:611-634`
     is compiled out);
   - `list_add(&wg->device_list)` (`:371`), `priv_destructor = wg_destruct`
     (`:376`) — assigned last so a failing `register_netdevice` does not call
     it (`dev.c:10686-10687`).
   - Failure arms (`:381-399`): every one is an allocation outcome (A's
     domain, section 11), unwound in reverse. `register_netdevice` itself
     cannot fail for a free name with a valid MTU on this path.

**Observable at once:** the ACK is 0; `wg_get` now finds the device
(`lookup_interface`, `netlink.c:52-73`, `dev_get_by_name` at `:63`) and
dumps `ifindex`, `listen_port` 0, `fwmark` 0, no keys, no peers. The
`update_gen` is 1, not the mirror's current default 0 (`Types.lean:274`);
nothing observes it (`netlink.c:222` puts it in `cb->seq`, read only by the
dump-interrupted check, which the harness does not decode), but the data
correspondence is wrong by one and L fixes it [AGENT].

### 2.2 Down and up again

**Down.** The guest's `wg_up` is `ioctl(SEND_FD, SIOCSIFFLAGS)` with the
flags read before the window (`guest.c:645-650,675-681`); `wg_down` is the
same with `IFF_UP` cleared. `dev_ifsioc` (`dev_ioctl.c:524-525`) →
`dev_change_flags` (`dev.c:9032-9045`) → `__dev_change_flags` (`:8962-8964`)
→ `__dev_close` → `__dev_close_many` (`:1599-1641`): `NETDEV_GOING_DOWN`
(`:1610`), **`clear_bit(__LINK_STATE_START)`** (`:1612`, so `netif_running`
is false before and during `wg_stop`), `dev_deactivate_many` (`:1623`),
**`ndo_stop` = `wg_stop`** (`:1635-1636`), `flags &= ~IFF_UP` (`:1638`).
Then `__dev_notify_flags` (`:8994-9008`) sends `NETDEV_DOWN` (`:9007`).

`wg_stop` (`device.c:115-135`), per peer (`:122-128`):
`wg_packet_purge_staged_packets` (`send.c:333-340`: `tx_dropped += qlen`),
`wg_timers_stop` (`timers.c:235-243`: `timer_delete_sync` ×5 and
`flush_work(&clear_peer_work)`), `wg_noise_handshake_clear` (`noise.c:88-96`:
index entry removed, handshake zeroed), `wg_noise_keypairs_clear`,
`wg_noise_reset_last_sent_handshake` (a kind-208 clock record at `noise.h:103`,
site `.resetLastSent`, one per peer). Then the handshake ring is drained
(`:130-131`, one `ptr_ring_consume` per queued message), `handshake_queue_len
= 0` (`:132`), and `wg_socket_reinit(wg, NULL, NULL)` (`:133`; `socket.c:419-437`)
frees both sockets after `synchronize_net()` (`:434`), which **does not
sleep on this kernel**: with `rtnl` held it is `synchronize_rcu_expedited`,
otherwise `synchronize_rcu`, and Tiny RCU's `synchronize_rcu` only advances
`gp_seq` (`kernel/rcu/tiny.c:150-159`; no `might_resched` under
`PREEMPT_NONE`). **`incoming_port` is
not changed** (`:431-432` writes it only when `new4` is set), so a later open
rebinds the same port, including a port that was drawn at random the first
time. The encrypt, decrypt and tx queues are not purged.

**What the notifiers do to the fixture** (environment, not WireGuard):
`fib_netdev_event(NETDEV_DOWN)` → `fib_disable_ip(dev, NETDEV_DOWN, false)`
(`fib_frontend.c:1508-1509`, `:1436-1444`) marks every nexthop on wg0 dead
and flushes, which **removes the fixture's IPv4 default route and the local
route of wg0's address**; the IPv4 address itself stays.
`addrconf_notify(NETDEV_DOWN)` → `addrconf_ifdown(dev, 0)`: with
`keep_addr_on_down` 0 everywhere (`addrconf.c:3912-3919`) **the IPv6 address
is removed**, and `fib6_ifdown` removes the single-nexthop IPv6 default
route (`route.c:4921-4925`). So after a down, the sender's `sendto` to any
destination that was routed into wg0 fails with `-ENETUNREACH` for both
families, and `wg_xmit` is never reached.

**Up again.** `__dev_open` (`dev.c:1519-1566`): `set_bit(__LINK_STATE_START)`
(`:1546`), `ndo_open` = `wg_open` (`:1551-1552`); on error the bit is cleared
and the flags unchanged (`:1556-1557`); on success `IFF_UP`, `dev_activate`
(`:1559-1561`), then `NETDEV_UP`, where `fib_netdev_event` re-adds the local
routes of the surviving IPv4 address (`fib_frontend.c:1500`) but **not the
default routes**. `addrconf_dev_config` admits `ARPHRD_NONE`
(`addrconf.c:3495-3504`) and proceeds; **no link-local address is added only
because `wg_open` set `addr_gen_mode = IN6_ADDR_GEN_MODE_NONE`**
(`device.c:47-48`) before `NETDEV_UP`. `ipv6_mc_up` draws nothing: the
all-nodes groups carry `MAF_NOREPORT` (`mcast.c:906`) and
`igmp6_group_added` returns on it (`:688`, `:724`). `wg_open`
(`device.c:31-62`): `wg_socket_init(wg,
incoming_port)` (`:51`); on error `goto out` with the error (so a
`-EADDRINUSE` makes the `ioctl` fail and leaves the device down); for each
peer `wg_packet_send_staged_packets` and, with a nonzero interval,
`wg_packet_send_keepalive` (`:54-58`). The staged queues are empty after a
down (purged at stop, and `wg_xmit` cannot stage while there is no route), so
the second open sends a keepalive per peer with an interval, which stages an
empty packet and, without a keypair, queues an initiation (`last_sent_handshake`
was reset at stop to 6 s in the past, so the rate limit passes). The mirror's
`wgOpen` (`Device.lean:43-55`) already has this control flow.

The guest must re-add the IPv6 address and both default routes after a
second successful up (`route_into_wg0`, `guest.c:396-432`, currently uses
`NLM_F_EXCL` for the addresses too and would fail with `EEXIST` on the
surviving IPv4 address). Section 6 gives the fail-closed rule.

### 2.3 The listen port on a running device; fwmark while up

`set_port` (`netlink.c:314-327`): `incoming_port == port` → 0 at once
(`:318-319`, also when running); else every peer's endpoint source is
cleared (`:320-321`; `socket.c:308-314`), and if `!netif_running` the port is
stored (`:322-325`), else **`wg_socket_init(wg, port)`** (`:326`). The
mirror has the first three arms (`Netlink.lean:93-103`) and stops at the
fourth with `unsupported "wg_socket_init"`.

`wg_socket_init` (`socket.c:349-417`): `creating_net` must be set
(`:376-381`, `-ENONET` otherwise; NULL only after `wg_destruct` or
`wg_netns_pre_exit`, so constant on our paths); `udp_sock_create(net,
&port4, &new4)` (`:387`) → `udp_sock_create4` (`udp_tunnel_core.c:11-55`):
`sock_create_kern` (`:18`), `kernel_bind` (`:31`) → `__inet_bind` →
`udp_v4_get_port` → `udp_lib_get_port` (`udp.c:240`; the IPv4 and IPv6 UDP
protocols share `net->ipv4.udp_table`, `udp.c:137-139`, `:3032`,
`ipv6/udp.c:1841`); a failure releases the socket and returns the error
(`:51-54`), which `wg_socket_init` passes up after a `pr_err` (`:388-391`;
hidden by `loglevel=3`; `printk` reads `local_clock`, which is not a hooked
reader). With IPv6 enabled, the IPv6 socket binds **the port the IPv4 socket
got** (`:397`, so one draw covers both), `v6only`; its `-EADDRINUSE` retries
the pair up to 100 times only when the requested port was 0 (`:401-402`).
Then `wg_socket_reinit(wg, new4, new6)` (`:412`): the pointers are swapped,
`incoming_port = inet_sport(new4)` (`:431-432`), `synchronize_net()`
(`:434`, no sleep: section 2.2), and the old sockets are released
(`:435-436`; `udp_tunnel_sock_release` and `sock_release` do not sleep
either). So `wg_socket_init` and `wg_socket_reinit` have **no sleep point**
on the modeled paths. The device keeps receiving throughout; the old sockets
are still bound while the new ones bind, which only matters for a random
draw (below).

**`-EADDRINUSE` is deterministic in the fixture.** `udp_lib_lport_inuse`
(`udp.c:142-170`) conflicts with a socket of the same netns at the same port
when neither has `SO_REUSEADDR` and `inet_rcv_saddr_equal(sk, sk2, true)`
(`inet_connection_sock.c:91`): a wildcard address matches any address
(`ipv4_rcv_saddr_equal`, `:78`; `ipv6_rcv_saddr_equal`, `:34`, where an
IPv4 socket counts as a mapped address and a dual-stack `::` socket matches
it). So wg0's IPv4 wildcard bind fails at **51999** (the fixture's
`127.0.0.1` listener) and at **51998** (the dual-stack `[::]` sender), and
succeeds at every other port; the subsequent `v6only` wildcard bind at the
same port then never conflicts (the `::1` listener is `v6only` at 51999,
already excluded; the sender is not `v6only`, but mapped-vs-`v6only`-any is
not a conflict). Ports below 1024 need `CAP_NET_BIND_SERVICE`
(`af_inet.c:510`), which the root fixture has. The environment therefore
owns a two-element set of bound ports, and `wg_socket_init`'s outcome is a
function of it.

In `wg_set_device` (`netlink.c:493-608`) the port change comes after
`device_update_gen++` (`:523`) and the fwmark block (`:525-531`) and before
peer removal and the private key; on `-EADDRINUSE` the call returns that
error with the earlier effects kept (`:533-538`). The mirror's order matches
(`Netlink.lean:220-229`). **Fwmark while up** needs nothing new: `send4`/
`send6` read `wg->fwmark` per packet (`socket.c:27,36`); the sockets carry no
mark; the dump shows it; the existing `.setDevFwmark*` decisions cover it.

**The random port** (`port == 0`, or an unset port at the first `wg_up`).
`udp_lib_get_port` (`udp.c:240-287`): `inet_sk_get_local_port_range`
(`:254`; `inet_connection_sock.c:130-150`: the netns range unless the socket
set `IP_LOCAL_PORT_RANGE`, which the kernel socket does not), default
`32768..60999` for every netns (`af_inet.c:1803`), `remaining = 28232`;
**one `get_random_u32()` draw** (`:257`); `first = reciprocal_scale(rand,
remaining) + low` = `low + ((rand × remaining) >> 32)` (`:258`); then the
candidate `first` is accepted iff no conflicting socket is bound at it and
it is not reserved (`:271-276`; the bitmap is indexed by `port >> log` within
the port's hash slot, which identifies the port exactly). Only on a conflict
does the C step by an odd multiple of the table size (`:262-263,277`), a
value that depends on the boot-time table size. The chosen port is
observable (the dump; the source port of wg0's datagrams). So the draw is a
**mirror site whose consumption is a computation**: the mirror consumes the
u32, computes `first`, and if `first` is one of the bound ports (51998,
51999, or wg0's own old port during a running rebind) stops with
`unsupported "the random port draw collides with a bound port"` — a
fail-noisy exit with probability about 7 × 10⁻⁵ per draw, below the cut.
Steering (section 3.3) makes the port a chosen value.

### 2.4 Deleting wg0: `RTM_DELLINK`

`rtnl_dellink` (`rtnetlink.c:3383-3436`): the device by name (`:3416`),
`-ENODEV` if absent (`:3422-3424`), `rtnl_delete_link` (`:3367-3380`):
WireGuard's `link_ops` has no `dellink` (`device.c:402-407`), so
`__rtnl_link_register` installed `unregister_netdevice_queue`
(`rtnetlink.c:530-531`; `dev.c:11478-11490`), and
`unregister_netdevice_many_notify` (`dev.c:11493-`) runs under `rtnl`:
1. **`dev_close_many`** (`:11526`; `:1652-1665`): a down device is skipped
   (`:1658-1659`); an up one goes through `__dev_close_many` → **`wg_stop`**
   (section 2.2) and `NETDEV_DOWN` (`:1665`). So deleting an up device is
   `wg_stop` then `wg_destruct`, in one task.
2. `unlist_netdevice`, `NETREG_UNREGISTERING` (`:11530-11531`),
   `flush_all_backlogs` (`:11533`, a `system_highpri_wq` work outside the
   armed set, which the task **waits for**: a sleep point), `synchronize_net`
   (`:11535`, no sleep: section 2.2), `NETDEV_UNREGISTER` (`:11552`):
   `inetdev_destroy` and `addrconf_ifdown(dev, 1)` remove the addresses;
   `fib_disable_ip(…, NETDEV_UNREGISTER, true)` and `fib6_ifdown`
   (`route.c:4919-4920`) remove every route via wg0; the neighbour parms are
   released. The `RTM_DELLINK` notification is built and sent.
3. `rtnl_unlock` → **`netdev_run_todo`** (`:10890-10954`): `__rtnl_unlock`
   (`:10912`), `rcu_barrier` (`:10916`), `netdev_wait_allrefs_any`
   (`:10931`; `:10798-10860`): returns at once when the refcount is 1;
   otherwise `rcu_barrier` and a doubling `msleep` from 1 ms to 250 ms
   (`:10784-10785`, `:10840-10847`). The IPv4 and IPv6 device structures
   drop their references in RCU callbacks, which the first `rcu_barrier`
   runs. Then **`priv_destructor` = `wg_destruct`** (`:10942-10943`).
4. **`wg_destruct`** (`device.c:242-270`): `list_del(&device_list)` under
   `rtnl` (`:246-248`), `creating_net = NULL` (`:250`), **`incoming_port =
   0`** (`:251`), `wg_socket_reinit(NULL, NULL)` (`:252`; a no-op after
   `wg_stop`, with another `synchronize_net`), **`wg_peer_remove_all`**
   (`:254`; `peer.c:167-184`: `wg_allowedips_free`, every peer made dead,
   `synchronize_net`, then `peer_remove_after_dead` per peer, `:94-150`:
   keypairs cleared, `wg_timers_stop`, `flush_workqueue(packet_crypt_wq)`
   twice, `napi_disable`/`netif_napi_del`, `flush_workqueue(handshake_send_wq)`,
   `--num_peers`, `wg_peer_put`), **`destroy_workqueue` ×3** (`:255-257`;
   `workqueue.c:5890-`: `drain_workqueue` at `:5907` runs any queued work on
   a kworker, where the dispatch hook opens a section if the function is in
   the armed set; `kthread_stop` of the rescuer at `:5919`),
   `wg_packet_queue_free` ×3 (`:258-260`; `queueing.c:43-48`: the handshake
   ring is purged, the crypt rings must be empty, `WARN_ON` otherwise),
   `rcu_barrier` (`:261`), **`wg_ratelimiter_uninit`** (`:262`;
   `ratelimiter.c:205-221`): when `--init_refcnt` reaches 0 (`:208`),
   `cancel_delayed_work_sync(&gc_work)` (`:211`),
   **`wg_ratelimiter_gc_entries(NULL)`** (`:212`; the function is `:55-83`)
   — whose first statement reads `ktime_get_coarse_boottime_ns()` (`:57`),
   **a kind-208 clock record in the deleting task**, value unused when
   `work` is NULL (`:65`, `:71` short-circuit on `unlikely(!work)`); the
   walk over the 2048 buckets with its two `hlist` loops and the `work`
   tests (`:62-82`) is task-context coverage, subject to A2 once
   `ratelimiter.c` is anchored (section 4.3) — then `rcu_barrier` (`:213`),
   the tables and the cache freed (`:214-218`)), `memzero_explicit(static_identity)`
   (`:263`), the two hashtables freed (`:264-265`), `free_netdev` (`:269`).

   The sleep points of the deletion are `flush_all_backlogs`, the
   `rcu_barrier`s (`dev.c:10916,10840`, `device.c:261`, `ratelimiter.c:213`),
   `kthread_stop` of the rescuer, `msleep` in `netdev_wait_allrefs_any`, and
   the flushes when work is pending. `synchronize_net` is not one.

All of it runs inside the trace process's `send()`: the ACK is queued after
`netdev_run_todo` returns, so after `wg_destruct` (no consequence for the
mirror), and the `recv()` reads it. The guest's end-of-trace `delete_wg0`
(`guest.c:204-215`) is the same message outside the window; with L it
becomes conditional on the device's existence.

**The inter-trace invariant has a condition** (audit M1). The strategy's
section 4.4 and the refcount claim of 2.1 hold only if **every network trace
process issues `RTM_DELLINK` before it exits**. Today a trace that `fail()`s
calls `_exit(1)` without `delete_wg0` (`guest.c:78-84`); the netns is then
torn down asynchronously by `cleanup_net` on a kworker
(`net_namespace.c:595,702`), possibly inside the next trace's window:
`wg_destruct` runs late, `init_refcnt` is skewed (the next creation draws no
key where the mirror expects one), and with D3 the dead device's timers
could fire as sections in the next trace. **Fix:** `fail()` in a process
whose network fixture is live performs a best-effort synchronous
`RTM_DELLINK` of `wg0` (errors ignored, no recursion into `fail`) before
`_exit`. Residual: a child killed by a signal still leaves the asynchronous
teardown; the next trace then sees a missing `.ratelimiterKey` record or a
section it does not expect — fail-noisy, not silent.

**Queued work at deletion.** The flushes in `peer_remove_after_dead` and
`drain_workqueue` run whatever is queued, in sections. The mirror's existing
rule for peer removal applies: pending handshake work makes the removal
`unsupported` (`Keypair.lean:143,154`), and pending crypt work is already
`unsupported` in every operation that does not wait for it
(`Env.requireNoCryptWork`). A queued `clear_peer_work` (D3's zero-key path)
runs synchronously in `wg_timers_stop`'s `flush_work`, as D3's design states
for `peer_remove_after_dead` (D3 section 5.1); L reuses that.

### 2.5 netns exit, PM and VM notifiers (out of scope, with reasons)

- **`wg_netns_pre_exit`** (`device.c:409-428`) runs from `cleanup_net`
  (`net_namespace.c:595`, `ops_pre_exit_list` at `:630-632`), a work item on
  `netns_wq` (`:416`, queued at `:702`) that runs after the last reference to
  a netns is dropped — for the fixture, after the trace process exits, when
  no window is open. Reaching it with a live `wg0` inside a window would need
  (a) `wg0` created from a different netns than the one it lives in
  (`IFLA_NET_NS_FD`; `creating_net` is the *creating* socket's netns,
  `rtnetlink.c:3635`), (b) the last reference to that netns dropped by an
  operation, and (c) `cleanup_net` in the armed dispatch set. Its effects
  (`netif_carrier_off`, `creating_net = NULL`, sockets released, endpoint
  sources cleared) then make `wg_socket_init` return `-ENONET`
  (`socket.c:380-381`), the only way to reach that arm. **Deferred**
  [AGENT]: a later target with its own small design; the arm is a constant
  `false` decision today, exact for the domain.
- **`wg_pm_notification`** is registered through `register_pm_notifier`
  (`device.c:438`), a stub returning 0 without `CONFIG_PM_SLEEP`
  (`suspend.h:473-478`); `PM` and `SUSPEND` are unset. **Unreachable on this
  config.** D3's option D (a suspend-style time injection) remains the only
  way to imitate its effect and is deferred there (D3 section 4.2).
- **`wg_vm_notification`** is registered through
  `register_random_vmfork_notifier` (`device.c:442`), a stub without
  `CONFIG_VMGENID` (`random.h:30-37`), which depends on `ACPI` (unset).
  **Unreachable on this config.**

### 2.6 Module init and exit: declared cuts

`CONFIG_WIREGUARD=y`, so `wg_mod_init` (`main.c:20-61`) runs at boot, before
any window, and `wg_mod_exit` (`:63-69`) never runs (`__exit`, no modules).
What they produce is in the mirror as constants or as resources below the
cut:
- `wg_allowedips_slab_init` (`allowedips.c:377`), `wg_peer_init`
  (`peer.c:230`): slab caches — allocation sites (`EnvSite.kmemCacheZallocNode`,
  `.kmemCacheZallocPeer`), A's domain;
- `wg_noise_init` (`noise.c:34-44`): `handshake_init_chaining_key` and
  `handshake_init_hash`, BLAKE2s of fixed strings — constants the mirror's
  `Handshake.lean` computes or embeds; a stated cut;
- `wg_device_init` (`device.c:434-463`): the two notifier stubs (2.5), the
  pernet ops (2.5), `rtnl_link_register` (the `dellink` default, 2.4) — the
  rtnetlink core is a cut; the mirror enters at `wg_setup`/`wg_newlink` and
  `wg_destruct`, with the core's `-EEXIST`/`-ENODEV` as environment outcomes;
- `wg_genetlink_init` (`netlink.c:636`): the family id the guest resolves at
  batch start (`guest.c:217-241`); the mirror enters at `wg_set_device` and
  the dump callbacks, as today (`Netlink.lean:5-19`).

No decision in these functions is reported, and `main.c` stays unanchored.

## 3. Hidden inputs

### 3.1 New sites (`HiddenSite`, `Defs.lean`)

| Site | Hook (record kind) | Consumer frame | Bytes | Role | Where consumed |
|---|---|---|---|---|---|
| `.cookieSecretBirthdate` | `ktime_get_coarse_with_offset` (208) | `drivers/net/wireguard/cookie.c:23` | 8 | mirror | `wgNewlink` → `cookieCheckerInit`; stored in `Device.cookieSecretBirthdate` |
| `.cookieSecret` | `get_random_bytes` (1) | `cookie.c:24` | 32 | mirror | same; stored in `Device.cookieSecret` (E reads it) |
| `.pubkeyHashKey` | `get_random_bytes` (1) | `peerlookup.c:29` | 16 | mirror | `wgNewlink`; stored in `Device.pubkeyHashKey` (data only; the bucket walk stays a cut, `Peer.lean:201-209`) |
| `.ratelimiterKey` | `get_random_bytes` (1) | `ratelimiter.c:192` | 16 | mirror | `wgNewlink` → `ratelimiterInit`, only when the refcount was 0; stored in `Kernel.ratelimiter.key` |
| `.ratelimiterGcNow` | `ktime_get_coarse_with_offset` (208) | `ratelimiter.c:57` | 8 | mirror | `wgDestruct` → `ratelimiterUninit` → `gcEntries none`, only when the refcount reaches 0; the first statement of the function; value unused in the `work == NULL` arm |
| `.udpPortDraw` | `get_random_u32` (104) | `net/ipv4/udp.c:257` | 4 | mirror (computed) | `socketInit` when the port is 0: `first = 32768 + ((rand × 28232) >> 32)` |
| `.neighReachTime` | `__get_random_u32_below` (110) | `net/core/neighbour.c:115` | 4 | **cut** | the `wg_create` cut point: **exactly two kind-110 records** (ARP and ND parms), each carrying the post-rejection value. Justification: **unobserved** — `reachable_time` is exported only in `IFLA_INET6_CACHEINFO` (and the IPv4 neighbour sysctls), which the harness never decodes, and no modeled path reads it |

The kinds are the existing ones of the `net-choice` kernel (`get_random_bytes`
1, `get_random_u32` 104, `__get_random_u32_below` 110 with one record per
call, the clock readers from 200 with `ktime_get_coarse_with_offset` at
208); no kernel change. The consumer-frame lines must be confirmed on the
built kernel by the Linux-only probe (section 11, step L0), as the D1/D2
sites were (`Defs.lean:301-311`); the table above is from source. L0's
checklist includes: the resolved consumer frames of the ratelimiter records
are `ratelimiter.c:57` and `ratelimiter.c:192` (E's design cites `:191-192`
for the same draw).

**Why the three WireGuard draws are mirror sites and not cuts:** they are
consumed by mirrored functions (`wg_newlink`, `wg_destruct`) at a fixed
position, exactly once per creation or last destruction, so exact
consumption costs nothing and keeps the inventory honest. The cookie secret
is data E needs: a cookie reply's MAC2 is keyed by it, so a device created
inside the window is what makes E's cookie paths exactly checkable (the
alternative is forcing a refresh with D3's advance, `cookie.c:96-101`,
120 s after creation).

### 3.2 Records already captured, and what `wg_down`/`wg_up` add

- `wg_stop`: one `.resetLastSent` (noise.h:103) per peer. Already a site.
- `wg_open` after a down: the keepalive/initiation path's existing sites.
- `wg_up` with a fixed port, `set_port` with a fixed port: **no records**
  (the socket path reads no hooked clock and draws nothing; today's `wg_up`
  passes the full check with exactly this path).
- `wg_delete`: `.resetLastSent` per peer if the device was up (through
  `wg_stop`), `.ratelimiterGcNow` once, plus whatever sections the flushes
  run (D3 workers; pending work is otherwise `unsupported`).
- Scheduler ambient (`.schedDlTimer`) wherever the task sleeps
  (`rcu_barrier`, `kthread_create`/`kthread_stop`, `flush_all_backlogs`,
  `msleep`; not `synchronize_net`): already declared, consumed anywhere.

### 3.3 Steering the random port [AGENT]

`harness/steer.py` gains the steerable site `udp_lib_get_port` (label
`udp_port_draw`), domain: any 4 bytes. The generator picks a port `p` in
`32768..60999` outside the bound set and supplies `rand = ceil((p − 32768) ·
2³² / 28232)`, checking `32768 + ((rand · 28232) >> 32) == p`. This is what
makes random-port traces useful: `wg_inject` names a literal port, so only a
steered trace can inject into a device that drew its port. Unsteered draws
observe the dump and the source port of wg0's datagrams. A steered collision
(`p` = 51999) is a **negative control**: the mirror stops with the
`unsupported` of section 2.3 and the run reports it, which shows the
fail-noisy exit fires rather than a wrong port being accepted.

## 4. The mirror

### 4.1 State

`Leanux/Kernel/Defs.lean`, `Kernel`:
- `wg : Option WG.Device` keeps its type; **`none` now also means "the
  network fixture has no wg0"**. `getDev` (`State.lean:9-12`) stays an
  invariant ("the C never dereferences one that is not there"): every entry
  point that the C reaches without a device tests `wg.isNone` first
  (`lookupInterface`'s `.lookupNoDev`, now a real decision; `Env.wgUp`,
  `Env.inject`, `Env.observe`, the `wgXmit` dispatch).
- `netIfindexNext : Nat` — the netns's cyclic cursor (`net->ifindex`): 4
  with the fixture's wg0, 3 in a bare fixture; `wgNewlink` takes it and
  increments. Netns state, so it lives in `Kernel`, not `Device`.
- `ratelimiter : { refcnt : Nat, key : List UInt8 }` — the global singleton
  (`ratelimiter.c:12-18`). `refcnt` is 1 with the fixture's wg0 (the key
  unknown, drawn before the window; zeros, never read by L) and 0 in a bare
  fixture. `tableSize` (2048 for the 256 MB guest, `:173-177`) is an
  environment constant in `Env.lean`, read by E's `gcEntries`.

`Leanux/WG/Types.lean`, `Device`:
- `sock4 sock6 : Option { port : Nat }` — the two socket pointers; `running`
  stays (`__LINK_STATE_START`). `wg_socket_reinit` sets `incomingPort` from
  `sock4` when present.
- `cookieSecret : List UInt8`, `cookieSecretBirthdate : Int`,
  `pubkeyHashKey : List UInt8` — from the three records; zeros/0 for the
  fixture's pre-created wg0 (unknown), which E must treat as "not observable
  unless the device was created in the window or the secret refreshed".
- `deviceUpdateGen := 1` at creation (and in `initialKernel`), fixing the
  off-by-one.
- `creatingNet : Bool := true` — cleared only by `wgDestruct`; the
  `-ENONET` arm's operand.

`World` (fixture state, `Defs.lean:402-440`): `routesViaWg0 : Bool` — set
after a successful `wg_up` (the guest's `route_into_wg0`), cleared by
`wg_down`/`wg_delete` (the notifiers of 2.2 and 2.4). `SentDatagram` gains
`sport : Nat` recorded at the send cut (the socket's port at send time), and
`Env.deliverSent` uses it instead of the device's current port [AGENT: exact
data; today the two coincide because no operation both changes the port and
sends].

### 4.2 Functions (`Leanux/WG/Device.lean`, `Socket.lean` new, `Netlink.lean`)

| Mirror | C | Notes |
|---|---|---|
| `wgSetup` | `device.c:274-307` | straight-line: a `Device` with the fixture's name, `ifindex := netIfindexNext`, MTU, flags; no decisions |
| `wgNewlink` | `device.c:309-400` | `allowedipsInit`; `cookieCheckerInit` (two records); `deviceUpdateGen := 1`; `pubkeyHashtableAlloc` (record); `indexHashtableAlloc`; three `allocWorkqueue` and three `packetQueueInit` as `envOk` sites with decisions on device.c lines 326, 330, 335, 340, 345, 350, 355, 360 (`mayHaveSlept` at the crypt workqueue: `kthread_create`); `ratelimiterInit` (decision `.ratelimiterInitFirst` at `ratelimiter.c:161`; the key record when first); `registerNetdevice` as `envOk` with the decision at `:368`, then `skipCut [.neighReachTime]` for the two notifier draws; `priv_destructor` has no mirror (the mirror's `wgDestruct` is called by the `wg_delete` operation); the unwinding arms mirror `:381-399` (the refcount decrement in `ratelimiterInit`'s failure, `ratelimiter.c:200`) |
| `wgCreate` (op) | `rtnetlink.c:3787-3791`, `3581-3671` | `if wg.isSome then return -EEXIST` (core; no WG decision), else `wgSetup`, `wgNewlink`, install `some device` |
| `socketInit port` | `socket.c:349-417` | `.socketInitNoNet` (`!creatingNet`, constant false); `.socketInitV4Err` decided by the environment's bound-port set (`Env.portBound`), returning `-EADDRINUSE`; for `port == 0` the draw and `first`; `.socketInitHasIpv6` (true); `.socketInitV6Err` (false; a true outcome is `unsupported "the IPv6 bind failed after the IPv4 one succeeded"`); `socketReinit (some {port}) (some {port})` |
| `socketReinit new4 new6` | `socket.c:419-437` | `.reinitHasNew4`; **no `mayHaveSlept`** (`synchronize_net` does not sleep here, section 2.2; claiming a sleep where there is none would be fail-open); `.sockFreeNull` ×2 for the old sockets |
| `setPort` running arm | `netlink.c:326` | replaces `unsupported "wg_socket_init"` by `socketInit port` |
| `wgOpen` | `device.c:31-62` | `socketInit d.incomingPort` replaces the `unsupported` for port 0 and the constant `.openSocketError false`; on error `return ret` |
| `wgUp` / `wgDown` | `dev.c:1519-1566`, `:1599-1641`, `:8994-9008` | `wgUp`: `running := true`, `wgOpen`, on error `running := false`; `wgDown`: `running := false`, `wgStop`; the notifier effects are `Env` (routes) |
| `wgStop` | `device.c:115-135` | per peer (`.stopPeersIter`): `purgeStagedPackets` (`txDropped += staged.length`, `staged := []`), `timersStop` (D3: clear the five timers; a queued clear work runs here through `runWorker .clearPeerWorker`), `handshakeClear` (`indexRemove .handshake`, `handshakeZero`), `keypairsClear`, `resetLastSentHandshake`; the drain loop (`.stopDrainIter` per queued message), `handshakeQueue := []`; `socketReinit none none` |
| `wgDestruct` | `device.c:242-270` | `creatingNet := false`, `incomingPort := 0`, `socketReinit none none`, `peerRemoveAll` (exists), destroy/free as cuts (`mayHaveSlept`: `kthread_stop`, `rcu_barrier`; crypt rings must be empty: `invariant` otherwise, the C's `WARN_ON`), `ratelimiterUninit` (`.ratelimiterUninitLast` at `ratelimiter.c:208`; when last: **`gcEntries none`** — E's function, which consumes `.ratelimiterGcNow` first (`:57`) and walks the `tableSize` buckets with the `work` tests, `:62-82`, as repeatable decisions; with no entries every inner loop is empty — then `mayHaveSlept` for the `rcu_barrier` at `:213`), `wg := none` |
| `wgDelete` (op) | `rtnetlink.c:3383-3436`, `dev.c:11493-` | `if wg.isNone then return -ENODEV`; `if running then wgDown`; `mayHaveSlept` (`flush_all_backlogs`, the `rcu_barrier`s of `netdev_run_todo`); `wgDestruct`; `Env.routesViaWg0 := false`; return 0 |
| `lookupInterface` | `netlink.c:52-73` | `.lookupNoDev (wg.isNone)` → `-ENODEV` |

Everything else in `wg_set_device`, `set_peer`, `wg_open`'s peer loop and
`wg_xmit` is unchanged.

### 4.3 Decisions and the instrumentation map

`correspondence/kcov.json` gains the functions `wg_newlink`, `wg_stop`,
`wg_destruct`, `wg_socket_init`, `wg_socket_reinit`, `wg_ratelimiter_init`,
`wg_ratelimiter_uninit`, **`wg_ratelimiter_gc_entries`**, and the anchored
file `drivers/net/wireguard/ratelimiter.c`. Anchoring the file puts the
task-context `wg_ratelimiter_gc_entries(NULL)` inside `wg_delete` under A2
(audit M2), so the GC's loop needs a mirror the moment `wg_delete` exists.
Ownership [AGENT, to agree with E]: E owns `gcEntries` (its design already
cites the file); L lists the function and, if E's `gcEntries` has not landed
when L integrates, adds the minimal version (the record, the bucket loop over
`tableSize` with empty inner loops, the `work` tests) that E then extends
with entries. `wg_ratelimiter_allow` stays E's. `wg_setup` owns no decision
and is not listed. `set_port` and `wg_open` are already listed. A2's rule
that a decision function Linux ran must report something
(`check.py:594-601`) then covers the new functions; the rtnetlink and
`dev.c` core stay unanchored, so their coverage is not checked (a cut, as
the netlink core is today).

New `Decision` constructors (`Decision.lean`), each with its condition line
and spans, following the existing `d` table form: `newlinkPeerHashtableErr`
(326), `newlinkIndexHashtableErr` (330), `newlinkRecvWqErr` (335),
`newlinkSendWqErr` (340), `newlinkCryptWqErr` (345), `newlinkEncryptQueueErr`
(350), `newlinkDecryptQueueErr` (355), `newlinkHandshakeQueueErr` (360),
`newlinkRatelimiterErr` (364), `newlinkRegisterErr` (368);
`ratelimiterInitFirst` (ratelimiter.c:161), `ratelimiterInitCacheErr` (165),
`ratelimiterInitTableV4Err` (180), `ratelimiterInitTableV6Err` (185),
`ratelimiterUninitLast` (208); the GC's `gcBucketIter` (62),
`gcV4EntryIter` (64), `gcV4Expired` (65), `gcV6EntryIter` (70),
`gcV6Expired` (71), `gcHasWork` (77, 80), all repeatable (E's names
prevail); `stopPeersIter` (device.c:122),
`stopDrainIter` (130); `socketInitNoNet` (socket.c:380), `socketInitV4Err`
(388), `socketInitHasIpv6` (396), `socketInitV6Err` (399),
`socketInitRetry` (401); `reinitHasNew4` (431), `sockFreeNull` (336,
repeatable). The existing `openSocketError` (device.c:52) becomes a real
outcome of `socketInit`, and `setPortNotRunning`'s false arm (netlink.c:326)
is reached.

## 5. Environment rules (`Leanux/Env.lean`)

Only fixture facts, stated as rules with their kernel reason:
- **Bound ports.** `portBound p := p == LISTEN_PORT || p == SENDER_PORT`
  (section 2.3). `socketInit` consults it. `Env.wgUp`'s two `unsupported`s
  for the fixture's ports (`Env.lean:335-336`) are removed: the outcome is
  now the C's `-EADDRINUSE`. For a random draw, the collision set also holds
  wg0's own `incomingPort` while `sock4` is set (a running rebind to port 0).
- **Routes.** `wg_xmit`'s dispatch returns `-ENETUNREACH` when
  `!routesViaWg0` (today: `!running`, `Syscalls.lean:95`). Set by the
  `wg_up` operation after a successful open (the guest adds the routes after
  the window, `guest.c:722-726`); cleared by `wg_down` and `wg_delete`
  (section 2.2, 2.4). A trace that goes up, down and up again has routes
  again after the second up.
- **Already up / already down.** `wg_up` on an up device: `__dev_change_flags`
  sees no `IFF_UP` change (`dev.c:8962`) and returns 0 with nothing done;
  `wg_down` on a down device likewise. `Env.wgUp`'s `unsupported "wg0 is
  already up"` (`Env.lean:334`) becomes `return 0` with no decisions beyond
  the fd's. `wg_up`/`wg_down` without a device: `-ENODEV` from
  `dev_ifsioc` (`dev_load` requests no module: `request_module` is `-ENOSYS`
  without `CONFIG_MODULES`, `kmod.h:30`, and `dev_ioctl.c:618-632` ignores
  the result).
- **Inject while down or absent.** No socket at the port: the datagram is
  answered by ICMP inside the sender's `sendto` (unsupported today,
  `Env.lean:482`; unchanged — the message stays "a datagram to a port other
  than wg0's"; the device being down is one such case).
- **Observe without a device.** `stats` is `null` in both the guest and the
  mirror; the listeners and the sender drain as before.
- **Timers at down** (D3): `wgStop` clears the five timer fields, so no
  firing is expected afterwards; a timer section for a cleared timer is a
  hidden mismatch, as D3 defines.
- **Sleep points** (`mayHaveSlept`, `State.lean:53-55`; audit m1). On this
  kernel `synchronize_net` does not sleep (section 2.2), so it is never a
  reason to call `mayHaveSlept`. The real sleep points on L's paths are
  `rcu_barrier`, `kthread_create`/`kthread_stop` (`workqueue.c:5624,5919`),
  `flush_all_backlogs` (`dev.c:11533`), `flush_work`/`flush_workqueue` when
  work is pending, and `msleep` in `netdev_wait_allrefs_any`. `mayHaveSlept`
  is placed there and nowhere else. The existing comments at
  `Keypair.lean:144,155` ("synchronize_net(), flush_workqueue()") are
  corrected in stream M: the `synchronize_net`s do not sleep, and the
  flushes wait only for pending work, which the preceding `unsupported`
  excludes — so those two calls are dropped [AGENT], with the regression
  suites as the evidence that nothing depended on them.
- **Temporary rtnetlink descriptor** [AGENT]. `wg_create` and `wg_delete`
  need a `NETLINK_ROUTE` socket. The guest opens it at the lowest free
  descriptor **before** the operation's window and closes it **after**
  reading the counts, as `route_into_wg0` does today (`guest.c:385-387,
  396-432`); only the `send`/`recv` run inside the window. Their `fdget` on
  that descriptor is anchored coverage (`fs/file.c`), so the mirror must hold
  a fixture file there for the operation: `Env.withFixtureFd` computes the
  lowest free slot at or above `nextFd` from the mirrored table (what
  `alloc_fd` returns; no decision is reported, as none ran in the window),
  installs a fixture file, runs the request through `socketCallOn`, and
  removes it. `nextFd` is restored by the close (`__put_unused_fd`), so no
  residue. If no slot below `rlimit_nofile` is free the guest fails the trace
  (environment failure) and the mirror is `unsupported`. The alternative, a
  persistent rtnetlink socket at descriptor 8 for every network trace, shifts
  the descriptor layout of all existing network traces and the Runner's
  literal domain (`Runner.lean:70`); not taken.

## 6. Harness and guest

- **Trace format** (`harness/trace.py`): operations `wg_create {op}`,
  `wg_down {op}`, `wg_delete {op}`, wire opcodes **15, 16, 17** (D3 takes 14
  for `wg_advance`; `FIELDS` order defines `OPCODES`, so L appends after
  D3's entry — a coordination point, not a conflict). An optional top-level
  field `"net_fixture": "bare"` (default `"wg0"`): the fixture creates the
  namespace, `lo` and the sockets but **not** `wg0`; valid only on network
  traces. The `T` line's `net` field becomes 0/1/2.
- **Guest** (`harness/guest.c`): `network_fixture(bare)` skips the
  `RTM_NEWLINK`; opcode 15/17 open the temporary rtnetlink socket before the
  window and close it after; the `SIOCGIFFLAGS` pre-read for `wg_up`/`wg_down`
  tolerates `ENODEV` (the operation then issues `SIOCSIFFLAGS` and reports
  its error); after a successful up, `route_into_wg0(first)`, where
  **`first` means "no successful up since this device instance was
  created"**: it is reset by the fixture's creation, by `wg_create` and by
  `wg_delete`, and a failed up does not clear it — on a first up both
  addresses and both routes with `NLM_F_EXCL`; on a later up the IPv4
  address add **must** fail with `EEXIST` and the IPv6 address and both
  routes must succeed (fail-closed: any other combination is an environment
  failure, since it would mean the kernel's keep-on-down behaviour differs
  from section 2.2); `print_stats` maps **exactly `ENODEV`** from
  `RTM_GETLINK` to `stats: null` and fails the trace on any other error;
  `WG_IFINDEX` is no longer a constant: the guest resolves it with
  `SIOCGIFINDEX` after each successful create and after the fixture's own
  creation; the temporary rtnetlink socket of opcodes 15 and 17 is opened
  **without `SOCK_CLOEXEC`** (as `route_into_wg0`'s is, so the descriptor's
  close-on-exec bit stays clear, as the mirror's table has it); the
  end-of-trace `delete_wg0` runs only if `wg0` exists; **`fail()` performs
  the same best-effort synchronous `RTM_DELLINK` when the network fixture is
  live** (section 2.4, M1), guarded against recursion; `wg_create` and
  `wg_delete` print a `LEANUX_TIMING` row with their wall time. The trace
  bound is unchanged (the deletion runs inside it: section 10).
- **Harness** (`harness/linux.py`): `stats` may be `null`; the `-append`
  and the dispatch set are unchanged (D3's additions land independently).
  `harness/wg.py`: nothing (the dump decoder already carries `ifindex`).
  `harness/steer.py`: the `udp_lib_get_port` site (section 3.3).
- **Evaluator** (`evaluator/check.py`): nothing structural; the new sites are
  declared in the mirror's site table as today.
- **Runner** (`Leanux/Runner.lean`): the three operations; `initialKernel`
  takes the fixture mode; `Trace.net` includes the new ops.

## 7. Generator and corpus

**Generator** (`evaluator/generate.py`): a `lifecycle` class, 10% of the
WireGuard suite [AGENT], drawing from: bare start + `wg_create` + the usual
configuration; a down in the middle of a configured session (D1/D2
building blocks) followed by `wg_observe` (`tx_dropped`), `wg_get`, and
optionally `wg_up` again with a persistent keepalive peer; a `wg_set` with a
new `listen_port` while up (free port, a fixture port, or 0 steered); a
`wg_delete` at any point followed by `wg_get`/`wg_up`/`wg_xmit`/`wg_observe`
(`ENODEV`, `ENETUNREACH`, `stats: null`) and optionally a `wg_create` again
(ifindex 4). `wait_after_up` counts `wg_down`, `wg_create`, `wg_delete` at
0.1 s each (the create and delete have no worker to wait for, but the guest
keeps the uniform `QUEUE_WAIT_US` after operations that can queue work:
`wg_down` cannot, `wg_create` cannot, `wg_delete` cannot — so no wait, 0 s).
`rlimit_nofile` stays ≥ 10 for traces with lifecycle operations (the
temporary descriptor).

**Corpus** `corpus/wireguard/l_*.json` (`scripts/wg-l-corpus.py`):
- `l_create_get`: bare; `wg_get` (`ENODEV`), `wg_create`, `wg_get`
  (ifindex 3, port 0, no keys), `wg_set` as `b1_basic`, `wg_up`, observe.
- `l_create_twice`: bare; `wg_create`, `wg_create` (`EEXIST`).
- `l_create_random_port_steered`: bare; `wg_create`, `wg_set` without a
  port, `wg_up` with the draw steered to 40001; `wg_inject` an initiation to
  40001; observe (the response's source port 40001); `wg_get` (listen_port
  40001). `expect`: the response.
- `l_random_port_natural`: the same without steering, no inject: `wg_get`
  shows a port in `32768..60999` (the check compares it exactly against the
  mirror's computation from the record).
- `l_random_port_collision` (**negative control**): the draw steered so that
  `first` = 51999: the mirror stops `unsupported`; recorded as a control that
  must fail.
- `l_up_fixture_port`: `wg_set` port 51999, `wg_up` (`EADDRINUSE`, device
  stays down), `wg_xmit` (`ENETUNREACH`), `wg_set` port 51820, `wg_up` (0).
- `l_down_purges_staged`: a peer with an endpoint but no response: `wg_up`,
  `wg_xmit` ×2 (staged, an initiation sent), `wg_down`, `wg_observe`
  (`tx_dropped` 2), `wg_get` (port kept), `wg_xmit` (`ENETUNREACH`).
- `l_down_up_keepalive`: `b1_keepalive_at_up`'s configuration; `wg_up`,
  observe (a keepalive's initiation), `wg_down`, `wg_up`, observe (another
  initiation: `last_sent_handshake` was reset at stop).
- `l_down_after_session` (D1 building block): a completed session, `wg_down`,
  `wg_up`, inject a data message under the old keys: dropped (the index
  lookup misses); `wg_xmit` initiates afresh.
- `l_set_port_running`: `wg_up` on 51820, `wg_set` port 51821, `wg_get`,
  `wg_xmit` (the initiation's source port at the listener is 51821; the
  fixture's listener sees the datagram, the sender's `recvfrom` would show
  the port if the endpoint were the sender).
- `l_set_port_running_same`: `wg_set` with the current port: no socket
  change (the `.setPortSame` arm, already reached today while down).
- `l_set_port_running_inuse`: `wg_set` port 51998 while up: `EADDRINUSE`;
  the old sockets keep working (`wg_xmit` still sends from 51820); the
  fwmark set in the same `wg_set` took effect (`wg_get`).
- `l_set_port_running_random_steered`: `wg_set` port 0 while up, steered to
  40002; `wg_inject` to 40002.
- `l_fwmark_running`: `wg_set` fwmark while up; `wg_get`.
- `l_delete_down`, `l_delete_up`: `wg_delete` of a down and of an up device
  (the latter after a session: `wg_stop` first), then `wg_get` (`ENODEV`),
  `wg_up` (`ENODEV`), `wg_xmit` (`ENETUNREACH`), `wg_observe` (`stats: null`).
- `l_delete_create`: `wg_delete`, `wg_create`, `wg_get` (ifindex 4), `wg_set`,
  `wg_up`, a session: the ratelimiter key is drawn again.
- `l_delete_absent`: bare; `wg_delete` (`ENODEV`).
- With D3: `l_down_stops_timers`: an initiation sent (retransmit armed),
  `wg_down`, `wg_advance 1450`: no retransmit section; `l_delete_with_clear_work`
  after D3's zero-key firing: the clear work's section inside the `wg_delete`.

## 8. Evidence: what pays for itself

Each mutant names what no existing check catches; an `unsupported` counts as
rejected (`wg-mutants.py:8`).

- **L-M1** `wgStop` does not purge the staged queue: `tx_dropped` differs
  (`l_down_purges_staged`). Behaviour, A1.
- **L-M2** `wgStop` does not reset `last_sent_handshake`: the second open's
  initiation is rate-limited in the mirror, sent by Linux
  (`l_down_up_keepalive`), and the `.resetLastSent` record is unconsumed
  (hidden mismatch).
- **L-M3** `socketReinit` changes `incomingPort` when `new4` is NULL (sets
  it 0): the dump after a down differs; the second open draws a port the
  record stream does not have.
- **L-M4** `setPort` stores the port instead of binding when running: the
  bound-port outcome is missing (`l_set_port_running_inuse`: mirror 0, Linux
  `EADDRINUSE`) and the datagram's source port differs
  (`l_set_port_running`).
- **L-M5** the port computation uses `rand mod remaining` instead of
  `reciprocal_scale`: `listen_port` differs on every random-port trace
  (`l_random_port_natural`); the steered traces inject to the wrong port.
- **L-M6** `wgDestruct` leaves the ratelimiter refcount at 1: the second
  creation does not consume the key record (`l_delete_create`); hidden
  mismatch.
- **L-M7** `wgNewlink` sets `ifindex` to a constant 3: `l_delete_create`'s
  dump differs.
- **L-M8** `wgDelete` skips `wgStop` for an up device: `tx_dropped` is not
  observable afterwards (the device is gone) but the `.resetLastSent`
  records of `wg_stop` are left unconsumed: hidden mismatch (`l_delete_up`).
- **L-M9** `wgOpen` on error leaves `running` true: the following `wg_xmit`
  reaches `wg_xmit` in the mirror and `ENETUNREACH` in Linux
  (`l_up_fixture_port`); and A2: Linux ran no `wg_xmit`.
- **L-M10** `deviceUpdateGen` starts at 0: **not rejected** by any check
  (unobservable); recorded as a known data-only correction, not claimed as
  evidence.
- **L-M11** `wgStop` does not clear the keypairs: in `l_down_after_session`
  the data message injected after down/up is decrypted and delivered by the
  mirror, dropped by Linux (the index lookup misses). Behaviour and A2.
- **L-M12** `wgStop` does not clear the handshake: a response to the old
  sender index injected after down/up is consumed by the mirror (the index
  entry is still there), while Linux's lookup misses. New trace
  `l_down_up_stale_response`: an initiation sent, `wg_down`, `wg_up`,
  inject a response naming the old index.
- **L-M13** `wgDown` does not clear `routesViaWg0`: the `wg_xmit` after a
  down reaches `wg_xmit` in the mirror and `ENETUNREACH` in Linux
  (`l_down_purges_staged`); A2 reports a decision function Linux did not
  run.
- **Controls:** `l_random_port_collision` (the `unsupported` fires);
  `l_create_twice` and `l_delete_absent` (core errors without WG coverage,
  only fd decisions: the A2 "no coverage in anchored files" rule is
  satisfied by `fdget`); the Linux-only probe's record inventory (section 11,
  L0) must show exactly the sites of section 3.1 and nothing undeclared, or
  the check's "choice from an undeclared consumer" fails.

**Not claimed:** `wg_stop`'s handshake-ring drain (a message queued without
its worker having run is `unsupported` already); the `-ENONET` arm; the
IPv6 bind retry.

## 9. Out of scope (fail-noisy), and why

| Item | Why it waits |
|---|---|
| `wg_netns_pre_exit`, `-ENONET` from `wg_socket_init` | asynchronous netns teardown; needs `cleanup_net` armed and a cross-netns creation (2.5) |
| `wg_pm_notification`, `wg_vm_notification` | unreachable on this config (no `PM_SLEEP`, no `VMGENID`) |
| a random port whose first candidate collides | the C's stepping depends on the boot-time UDP table size; probability ~7e-5; `unsupported`, with a steered control |
| the IPv6 bind failing after the IPv4 one succeeded (`socket.c:399-405`) | impossible in the fixture's socket set; `unsupported` if it happens |
| a second device (`wg1`), two devices sharing the ratelimiter | `Kernel.wg` stays single; the refcount is modeled so a later extension is data-only |
| deletion or down with pending work (handshake, crypt, NAPI) | the existing `unsupported`s; the flush-run sections are D3's clear worker only |
| `register_netdevice` failing (`-EEXIST` on the name is caught by the core; allocation outcomes) | A's domain; assumed success |
| creation with options (`IFLA_MTU`, `IFLA_ADDRESS`, another name, another netns) | the fixture's message is fixed; the mirror's `wgSetup` takes no attributes |
| `IFF_UP` changes with other flag bits, `SIOCSIFMTU`, `dev_change_net_namespace` | not in the operation set |
| `wg_stop` with packets in the crypt queues or NAPI | `requireNoCryptWork`; the in-flight `send4` `-ENONET` arm (`socket.c:41-43`) is never modeled |

## 10. Risks

- **High, and likely to materialise: the KCOV area in the create window**
  (audit M3). `CAPACITY` is 64 K words (`guest.c:31`): at most 65,535 PC
  hits or **16,383 comparison records** per operation, else
  `empty_or_full_kcov` (`guest.c:739-742`). `register_netdevice` registers
  about 130 sysctl entries (IPv4 and IPv6 device conf, neighbour parms),
  each inserted into an rb-tree by name comparison; `memcmp`/`strcmp` are
  instrumented one comparison record per byte, so that alone is roughly 7 k
  records, before sysfs and kobject work. The comparison child will very
  probably overflow. **Raising `CAPACITY` is therefore the default outcome
  of L0**, not a contingency: to 256 K words unless L0's counts say
  otherwise. The cost is the guest's static arrays (`guest.c:86-91`:
  `order` 16 B and `first` 1 B per word, `records` 40 B per 4 words) plus
  the two mapped areas: about 2.7 MB today, about 11 MB at 256 K words, in
  a 256 MB guest. A guest constant, no kernel change.
- **Low: the deletion's duration inside the 4 s bound** (downgraded by the
  audit). About four scheduler round trips (`rcu_barrier` ×3–4,
  `kthread_stop`), milliseconds on Tiny RCU; `netdev_wait_allrefs_any`'s
  `msleep` runs only if a reference lingers after the first barrier. L0's
  `LEANUX_TIMING` row confirms it; `wg_delete` gets no guest wait.
- **Medium: undeclared consumers in the registration path.** Section 2.1's
  inventory is from source; `register_netdevice` touches many subsystems. The
  L0 probe is the measurement, exactly as step 0 of the choice-stream
  strategy was; an undeclared consumer fails the check and is either a cut
  entry with a justification or a mirror site.
- **Low: the consumer-frame lines** (section 3.1) may shift under inlining
  (`neigh_rand_reach_time` is exported, `wg_cookie_checker_init` is
  cross-TU, so both keep their frames; `udp_lib_get_port` may inline into
  `udp_v4_get_port`, which keeps the file:line through DWARF). L0 confirms.
- **Low: the fixture rule for re-adding addresses.** If `keep_addr_on_down`
  or the IPv4 persistence differ from section 2.2, the guest fails closed and
  the rule is corrected.
- **Sequencing with D3.** `wgStop`'s `timersStop` and the clear worker use
  D3's timer fields and `Worker` constructors; L's mirror stream builds on
  D3's interface commit. L's kernel need is none, so L's kernel-side work is
  only the probe and the guest.

## 11. Execution plan

Worktree `task/l-life`; signoff at the end covering the merge only (no
oracle change). Dependencies: **D3** (timer fields, `Worker` + 6, opcode 14,
the D3 kernel for any trace that arms timers — every `wg_up` with a peer
does, so L's full check runs on the D3 kernel once D3's arm records are
consumed by the mirror); **E** (reads `Device.cookieSecret` and
`Kernel.ratelimiter`; owns `wg_ratelimiter_allow` and the GC; L owns the two
init functions and the anchoring of `ratelimiter.c`); **A** (the ten
`envOk` sites of `wg_newlink` and the three of `wg_ratelimiter_init` are
declared by L with assumed success; A's fault injection decides their
outcomes later).

**L0 — the Linux-only probe (first, needs one VM slot briefly):** the guest
gains opcodes 15–17, the bare fixture and the `fail()` teardown; a handful
of traces (bare create; create+up+delete; up+down+up; set_port running;
random port; `wg_up` on 51998 and on 51999) run on the current `net-choice`
kernel with a mirror that is not yet extended, in `--trace` mode.
Checklist:
- the record inventory per operation: sites, counts, consumer frames —
  in particular the ratelimiter records resolve to `ratelimiter.c:57` and
  `ratelimiter.c:192`, the port draw to `udp.c:257`, the two neighbour
  draws to `neighbour.c:115`, the cookie records to `cookie.c:23-24`, and
  nothing undeclared appears;
- the PC and comparison counts of the create and delete windows against
  `CAPACITY`, with the raise to 256 K words applied if either exceeds the
  bound (expected for the comparison child of `wg_create`);
- the `-EADDRINUSE` outcomes of `wg_up` on the two fixture ports;
- the first bare `wg_get`'s `ifindex` (3) and the index after
  delete+create (4);
- the wall time of `wg_create` and `wg_delete` (`LEANUX_TIMING`).

This settles sections 3.1 and 10 before any mirror code.

**Stream G — guest and harness** (`harness/guest.c`, `harness/trace.py`,
`harness/linux.py`, `harness/steer.py`, `harness/test_*.py`): section 6.

**Stream M — mirror** (`Leanux/WG/Device.lean`, new `Leanux/WG/Socket.lean`,
`Leanux/WG/Netlink.lean`, `Leanux/WG/Types.lean`, `Leanux/Kernel/Defs.lean`,
`Leanux/Kernel/Decision.lean`, `Leanux/Runner.lean`, `Leanux/Syscalls.lean`,
`Leanux/Env.lean`, `correspondence/kcov.json`): sections 4 and 5. On D3's
interface commit.

**Stream H — generator, corpus, mutants** (`evaluator/generate.py`,
`scripts/wg-l-corpus.py`, `corpus/wireguard/l_*.json`, `scripts/wg-mutants.py`):
sections 7 and 8.

**Integration:** the full check (all suites, since `Env.wgUp`'s rules
changed and `initialKernel` gained fields), all mutants, the steering
controls plus `l_random_port_collision`, on the D3 kernel and boot
parameters; the report with the record inventory; signoff.

## 12. File ownership summary

| Area | L owns | Shared with |
|---|---|---|
| `harness/guest.c` | opcodes 15–17, bare fixture, ifindex resolution, re-up routes, `stats: null`, conditional teardown, `fail()` teardown, `CAPACITY`, timing row | D3 (opcode 14, the clocksource rows) — disjoint hunks |
| `harness/trace.py`, `harness/linux.py` | the three ops, `net_fixture`, `stats` null | D3 (`wg_advance`, `DISPATCH_SYMBOLS`) |
| `harness/steer.py` | the `udp_lib_get_port` site | — |
| `Leanux/WG/Device.lean`, `Socket.lean` (new) | `wgSetup`, `wgNewlink`, `wgStop`, `wgDestruct`, `socketInit`, `socketReinit`, `wgUp`/`wgDown` | D3 (`timersStop`'s body) |
| `Leanux/WG/Netlink.lean` | `setPort`'s running arm, `lookupInterface` | — |
| `Leanux/WG/Types.lean`, `Leanux/Kernel/Defs.lean` | sockets, cookie secret, pubkey key, `creatingNet`, `netIfindexNext`, `ratelimiter`, the seven sites | D3 (timer fields, `Worker`), E (reads) |
| `Leanux/Kernel/Decision.lean` | the decisions of section 4.3 | D3 (timer decisions) |
| `Leanux/Env.lean`, `Leanux/Syscalls.lean`, `Leanux/Runner.lean` | bound ports, routes, fixture fd, `stats: null`, the ops, `initialKernel` modes | D3 (`Env.advance`, `wgAdvance`) |
| `correspondence/kcov.json` | seven functions, `ratelimiter.c` | E (`wg_ratelimiter_allow`) |

## 13. Decisions for the user, and open questions

1. **Scope** (section 1) and the out-of-scope list (section 9), in
   particular: netns exit deferred; the PM/VM notifiers declared unreachable
   on this config; a single device.
2. **The random port as a computed mirror site** (section 2.3, 3.1): the
   mirror computes `first` from the recorded u32 and stops on a collision
   instead of modeling the UDP table's stepping. And **steering the port**
   as the way to inject into a device that drew its port.
3. **The bare fixture as a trace field** (`"net_fixture": "bare"`) rather
   than inferring it from a leading `wg_create` [AGENT: explicit over
   implicit].
4. **The temporary rtnetlink descriptor** opened and closed outside the
   window, mirrored as a decision-free fixture slot (section 5), rather than
   a ninth persistent fixture descriptor.
5. **Natural ifindex allocation** (`ifi_index` 0, cyclic: 3 then 4) with
   `Kernel.netIfindexNext`, rather than pinning `ifi_index = 3` in the
   fixture's message.
6. **`CAPACITY`**: permission to raise the guest's KCOV area to 256 K words
   as L0's default outcome (the create window's comparison child is expected
   to overflow the 16,383-record bound; about 11 MB of guest memory; section
   10).
9. **The `fail()` teardown** (section 2.4, M1): a best-effort synchronous
   `RTM_DELLINK` on every failure path of a network trace, as the condition
   under which the inter-trace invariant and the ratelimiter refcount claim
   hold.
7. **Question:** should `wg_delete` of an up device be allowed while
   timers are armed (every post-handshake device) — yes under D3, since
   `wg_stop` deletes them synchronously; without D3's fields the mirror
   cannot say which timers were pending, so L's mirror stream waits for
   D3's interface commit. Is that sequencing acceptable, or should L's
   guest/harness stream (G) and the L0 probe proceed now and M wait?
8. **Question:** E depends on `Device.cookieSecret` being known; L provides
   it only for devices created in the window. Should E's cookie traces be
   required to start bare and create the device (L's recommendation), or
   should E also plan the refresh-by-advance route?

## 14. Kernel claims that were inferred, with the audit's verdicts

Stated in the first draft so the review could target them; the audit's
answers are recorded here:
- The unbound `handshake_send_wq` **shares** `system_unbound_wq`'s pool
  (section 2.1): inferred from `get_unbound_pool`'s hash lookup and the
  default attributes. **Audit: plausible and harmless** — a new pool would
  create a worker thread, below the cut and unrecorded either way.
- `kobject_uevent` runs no usermode helper. **Audit: confirmed** —
  `lib/kobject_uevent.c:611-634` is compiled out without
  `CONFIG_UEVENT_HELPER`.
- `wg_ratelimiter_init`'s slab cache may merge with an existing one
  (`kmem_cache_create` aliasing): not observable; mentioned only to explain
  why `kmem_cache_destroy` may not free it. Not audited; no claim depends on
  it.
- The bind-conflict analysis (section 2.3). **Audit: the conclusion is
  correct** (`inet_connection_sock.c:76-80`, `:97-101`); L0's `wg_up` on
  51998 and 51999 still confirms the two outcomes directly.
- `addrconf_dev_config` and `ARPHRD_NONE`. **Audit: the first draft's
  mechanism was wrong** — the function admits `ARPHRD_NONE`
  (`addrconf.c:3495-3504`) and proceeds; no link-local address is added only
  because `wg_open` set `addr_gen_mode = NONE` (`device.c:47-48`), and
  `ipv6_mc_up` draws nothing (`MAF_NOREPORT`, `mcast.c:906,688,724`).
  Section 2.2 is corrected.
- `cleanup_net` runs only after the trace process exits. **Audit: holds
  except on the failure path** — a `fail()`ed trace exits without
  `delete_wg0`; section 2.4 (M1) states the condition and the fix.
- `sit0` is ifindex 2. **Audit: confirmed by the config.** L0's first bare
  `wg_get` still shows the created device's index.
- The deletion's duration: **downgraded** to about four scheduler round
  trips, milliseconds (section 10). The KCOV capacity: **upgraded** to a
  likely overflow of the create window's comparison child (section 10).

## 15. Audit record [AGENT 2026-10-05]

An independent audit of the first draft verified almost every kernel path
claim and found:
- **C1 (critical).** Every `ratelimiter.c` line number was wrong: the
  first draft's numbers came from a listing of `main.c` and `ratelimiter.c`
  concatenated, so each was 78 too high (the file is 223 lines). Corrected
  throughout: the GC is `:55-83` with its clock read at `:57`; init is
  `:158-203` (`++init_refcnt != 1` at `:161`, the cache at `:164-165`, the
  sizing at `:173-177`, the tables at `:179-185`, the GC queued at `:191`,
  the key drawn at `:192`, the failure decrement at `:200`); uninit is
  `:205-221` (the refcount test at `:208`, `cancel_delayed_work_sync` at
  `:211`, `gc_entries(NULL)` at `:212`, `rcu_barrier` at `:213`). The sites
  `.ratelimiterKey` and `.ratelimiterGcNow` are at `:192` and `:57`; L0's
  checklist requires the resolved consumer frames to equal them. (The audit
  quoted `:164` and `:181`/`:185` for the cache and table tests; the source
  has the tests at `:165`, `:180` and `:185`, which the decisions use.)
- **M1.** The refcount claim and the inter-trace invariant assumed every
  trace reaches teardown; a `fail()`ed trace does not. Now stated as a
  condition, with the best-effort synchronous `RTM_DELLINK` in `fail()`
  (sections 2.4, 6, 13.9).
- **M2.** Anchoring `ratelimiter.c` puts the task-context GC walk inside
  `wg_delete` under A2. Now: `wgDestruct` → `ratelimiterUninit` → E's
  `gcEntries none`, consuming `.ratelimiterGcNow` first; the function is
  listed; ownership with E stated (section 4.3).
- **M3.** The comparison-mode overflow of the create window is likely, not
  possible: about 130 sysctl registrations with per-byte comparison records.
  Raising `CAPACITY` is L0's default outcome; the memory figure corrected
  from "15 → 60 MB" to about 2.7 MB today and 11 MB at 256 K words
  (`guest.c:86-91`) (sections 10, 11, 13.6).
- **m1.** `synchronize_net` does not sleep on this kernel (Tiny RCU,
  `tiny.c:150-159`; no `might_resched` under `PREEMPT_NONE`), so
  `mayHaveSlept` at `socketReinit` was unjustified and fail-open. The real
  sleep points are listed in section 5 and placed in section 4.2; the
  `Keypair.lean:144,155` comments are corrected in stream M.
- **m2.** `addrconf_dev_config`'s mechanism corrected (section 2.2, 14).
- **m3.** The record kinds named: `get_random_bytes` 1, `get_random_u32`
  104, `__get_random_u32_below` 110 (one record per call, the post-rejection
  value; `.neighReachTime` is exactly two such records),
  `ktime_get_coarse_with_offset` 208; records are written only when
  `current` has KCOV enabled (section 3.1).
- **m4.** The `.neighReachTime` cut justified as "unobserved":
  `reachable_time` is exported in `IFLA_INET6_CACHEINFO`, which the harness
  never decodes (section 3.1).
- **m5.** Three mutants added: `wgStop` not clearing keypairs (L-M11), not
  clearing the handshake (L-M12, with a new trace), `wgDown` not clearing
  `routesViaWg0` (L-M13) (section 8).
- **m6.** The guest rules made fail-closed: `first` means no successful up
  since this device instance was created (reset at create and delete; a
  failed up does not count); `print_stats` maps exactly `ENODEV` to `null`;
  the temporary rtnetlink socket is opened without `SOCK_CLOEXEC`
  (section 6).
- **m7.** `Syscalls.lean:95` (not `:107`); for `RTM_DELLINK` the ACK follows
  `wg_destruct` (`rtnetlink_rcv` is `netlink_rcv_skb` with the per-message
  `rtnl` handling inside `rtnetlink_rcv_msg`), no consequence;
  `network_fixture` is at `guest.c:174-197` (sections 2.1, 2.4, 5).

## 16. Stream M results [AGENT 2026-10-06]

Branch `task/l-m`, on D3's interface commit (`task/d3`, `45f077a`) with
stream G (`task/l-g`) merged. Kernel: the D3 build
(`.artifacts/kernel-net-choice-d3`, `clocksource=refined-jiffies`),
`ARM_RECORDS` off as D3's interface has it.

### 16.1 The merge of stream G

Six files conflicted with D3's interface (`Leanux/Runner.lean`,
`Leanux/Syscalls.lean`, `evaluator/protocol.py`, `harness/guest.c`,
`harness/linux.py`, `harness/trace.py`). Both sides are kept: `wg_advance`
is opcode 14 and `wg_create`/`wg_down`/`wg_delete` 15-17; `FIELDS`,
`WG_OPS`, the Lean `Operation`/`Syscall`/`Trace` carry D3's `armRecords`
and G's `bare`; `SEMANTIC_ERRNOS` has D3's empty `wg_advance` set and G's
`ENODEV`/`EADDRINUSE` sets; `linux.py` collects both `LEANUX_CLOCKSOURCE`
and `LEANUX_TIMING`; `guest.c` keeps D3's advance case and clock beside G's
lifecycle cases and timing clock, and the rekey bound counts from the first
real up (G) minus the advances (D3). The unit tests pass; the full check
below covers the merged harness.

### 16.2 What was built (sections 4-5)

- State: `Device.sock4/sock6`, `creatingNet`, `cookieSecret`,
  `cookieSecretBirthdate`, `pubkeyHashKey`, `deviceUpdateGen := 1`;
  `Kernel.netIfindexNext`, `Kernel.ratelimiter {refcnt, key}`;
  `World.routesViaWg0`, `World.portBound` (supplied as `Env.portBound`);
  `SentDatagram.sport` (the socket's port at the send cut, which
  `Env.deliverSent` reports).
- Sites 120-126 (outside 64-115): the seven of section 3.1, with L0's
  consumer frames. `.neighReachTime` is a cut consumed by
  `skipCutExactly .neighReachTime 2` (exactly two records per creation, fail
  closed), rather than `skipCut`'s any number.
- `Leanux/WG/Socket.lean` (new): `socketReinit` with its decisions (no
  `mayHaveSlept`), `socketInit` (cut: the bound-port outcome, the random
  port computed from `.udpPortDraw`, `unsupported` on a collision with a
  fixture port or wg0's own sockets). `Leanux/WG/Device.lean`: `wgOpen`
  calls `socketInit`, `wgUp` undoes `running` on failure, `wgStop`,
  `wgDown`, `ratelimiterInit`, `gcEntries` (empty tables), `ratelimiterUninit`,
  `wgSetup`, `wgNewlink`, `wgCreate`, `wgDestruct`, `wgDelete`.
  `Netlink.lean`: `set_port`'s running arm binds; `lookupNoDev` is real.
  `Env.lean`: `portBound`, `wgUp`/`wgDown`/`wgDelete` with the routes,
  `ENODEV` without wg0, `stats: null`, no-device guards.
  `Syscalls.lean`: `rtnetlinkRequest` (the temporary descriptor of section
  5). `Runner.lean`: `initialKernel` with the bare mode. `Keypair.lean`: the
  two `mayHaveSlept` calls dropped with corrected comments (audit m1).
- Decisions (an `-- L stream M` block after the D3 regions): `wg_newlink`
  (326-368), `wg_stop` (122, 130), `wg_socket_reinit` (431) and `sock_free`
  (336), `wg_ratelimiter_init` (161-185), `wg_ratelimiter_uninit` (208, two
  operands), `wg_ratelimiter_gc_entries` (62, 64, 70, 77, 80).
  `correspondence/kcov.json`: `ratelimiter.c` anchored; `wg_newlink`,
  `wg_stop`, `wg_destruct`, `wg_socket_reinit`, `wg_ratelimiter_init`,
  `wg_ratelimiter_uninit`, `wg_ratelimiter_gc_entries` listed.
- Corpus: `scripts/wg-l-corpus.py`, 20 `corpus/wireguard/l_*.json` traces
  (section 7's list, plus `l_up_down_noop`, `l_create_delete_create` and
  `l_down_up_stale_response`; the two D3-dependent traces wait for D3's
  advance), and the control `corpus/lifecycle-controls/l_random_port_collision.json`.
- Mutants L-M1..M13 in `scripts/wg-mutants.py`, run on the `l_*` traces.

### 16.3 Deviations [AGENT]

- **`wg_socket_init` stays unlisted**, so `socketInitNoNet`, `V4Err`,
  `HasIpv6`, `V6Err` and `Retry` (4.3) are not reported. Listing it makes
  its inlined `maybe_get_net`/`put_net` PCs witnesses of the refcount
  decisions (`include/linux/refcount.h` 145-152, 264-275), whose declared
  comparisons need the namespace's reference count, which the mirror does
  not hold. Its outcomes are still checked by results, dumps and the
  datagrams' source ports.
- **`wg_ratelimiter_gc_entries` reports its first bucket only**: the 2048
  empty buckets' identical outcomes would exceed the protocol's bound of
  4096 branches per trace; the check treats a repeatable decision's
  outcomes as a set, so nothing is lost to it. `gcV4Expired`/`gcV6Expired`
  are E's (never evaluated with empty tables).
- **`lookup_interface.kind_mismatch`'s false span (72) removed**: 72's point
  is the epilogue the `-ENODEV` return shares, which the first bare
  `wg_get` showed.
- `wg_stop` with handshake messages queued for the receive worker is
  `unsupported` (the drain is not exercised); `wg_stop` with pending send
  work, crypt work, decrypt work or a scheduled NAPI poll is `unsupported`.
- The collision control is its own control suite (`lifecycle-controls`,
  run by `scripts/steering-controls.py`): a stopped mirror fails its whole
  chunk, so it cannot share a chunk with traces that must agree.
- Not done: the generator's `lifecycle` class (section 7) and the D3
  traces `l_down_stops_timers`, `l_delete_with_clear_work`.
- Armed chunks with lifecycle traces [AGENT 2026-10-12], seen first at the W
  batch's claim point, where `w8_exit_delete` was the first `wg_delete` in
  one: the last device's `wg_delete` allocates one dentry below the cut
  (`wg_ratelimiter_uninit` -> `kmem_cache_destroy` -> `debugfs_slab_release`
  -> `lookup_slow`, consumer `fs/namei.c:1730`), consumed at
  `ratelimiterUninit` as the alloc cut site `dAllocSlabDebugfs` when a chunk
  arms the dentry cache's range; `wg_create`'s `register_netdevice` has
  `devinet_sysctl_register`'s netconf notification (`nlmsg_new`) between its
  two `neigh_parms_alloc` draws (`skipCutExactly`'s `between` cuts); and an
  up device's `wg_delete` has the `dev_close_many` and `NETDEV_UNREGISTER`
  notifications between `wg_stop`'s last clock read and `wg_destruct`
  (`wgDelete`'s cut before `flush_all_backlogs`). The net device's uevents
  (`kobject_uevent_env` -> `alloc_uevent_skb`, `lib/kobject_uevent.c:289`,
  the device and its queues at `netdev_register_kobject` and
  `netdev_unregister_kobject`) are the alloc cut site `allocUeventSkb`,
  consumed at those same two cuts.

### 16.4 Evidence

- Full check, all suites, on the D3 kernel at `563d930`
  (`.artifacts/lm-full1`): **1389 of 1389 agree** (the 1369 existing traces
  and the 20 `l_*`), 39389 operations, 323466 operand pairs, 4 output-limit
  chunk splits, no timed-out chunk. Cut records skipped include
  `neigh_reach_time` 14 (7 creations × 2).
- Mutants (`l_*` traces): L-M1..M9 and L-M11..M13 rejected (hidden
  mismatch: M1, M2, M3, M4, M6, M8, M12, M13; unsupported: M5, M11;
  semantic mismatch: M7, M9). L-M10 passes, as expected (not claimed).
- Controls: the three steering controls and `l_random_port_collision`
  (`unsupported_path`: "the random port draw collides with a bound port")
  are rejected.

### 16.5 The generator class [AGENT 2026-10-12]

`lifecycle_trace` (`evaluator/generate.py`, `LIFECYCLE_SHARE` 0.1 as section
7 sized it): a bare start with `wg_create` (twice for `EEXIST`, or
create-delete-create for ifindex 4) and the usual configuration and
transmissions; a down in the middle with the observation, the dump, a
transmission that fails and optionally an up again; a port while running
(free, the listener's or the sender's for `EADDRINUSE`, the same, or 0 with
`udp_port_draw` steered to 40001-40019); a delete at any point followed by
operations on the missing device and optionally a create again; and W3's
queue-then-remove (docs/2026-10-06-w3-w12.md V.6). 200/200 pass the domain
filter. The counts in `wait_after_up` stay 0 for the lifecycle operations
(no guest wait), and 1.1 s for `wg_netns_close` (W8).
