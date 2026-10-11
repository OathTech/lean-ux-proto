import Leanux.WG.State

/-!
# drivers/net/wireguard/socket.c — wg0's UDP sockets (L)

`wg_socket_init` (socket.c:349-417) and `wg_socket_reinit` (419-437),
docs/2026-10-05-l-lifecycle.md, section 2.3.

`wg_socket_init` is a cut point: `udp_sock_create` binds a wildcard IPv4
socket, then a `v6only` wildcard IPv6 socket at the port the first got. Its
outcome is decided by the fixture's bound ports (`World.portBound`, the
environment's `Env.portBound`): `-EADDRINUSE` exactly at a port a conflicting
socket holds. The function stays unlisted in `correspondence/kcov.json`: its
inlined `maybe_get_net`/`put_net` compare the namespace's reference count,
a value the mirror does not hold, at `include/linux/refcount.h` lines the
refcount decisions own, so its own decisions (`-ENONET`, the two binds, the
IPv6 retry) are not reported [AGENT, a deviation from the design's 4.3].
`wg_socket_reinit` is mirrored with its decisions.
-/

namespace Leanux.WG
open Leanux

/-- sock_free (socket.c:334-340), inlined into wg_socket_reinit:
    `sk_clear_memalloc` and `udp_tunnel_sock_release` are cut points. -/
def sockFree (sock : Option Nat) : M Unit := do
  if ← branch .sockFreeNull sock.isNone then return

/-- wg_socket_reinit (socket.c:419-437): swap the socket pointers, take
    `incoming_port` from the new IPv4 socket, free the old ones.
    `synchronize_net()` (434) does not sleep on this kernel (Tiny RCU,
    `CONFIG_PREEMPT_NONE`; design section 2.2), so it is no `mayHaveSlept`. -/
def socketReinit (new4 new6 : Option Nat) : M Unit := do
  let d ← getDev
  let (old4, old6) := (d.sock4, d.sock6)
  modifyDev fun d => { d with sock4 := new4, sock6 := new6 }
  if ← branch .reinitHasNew4 new4.isSome then
    let some port := new4 | invariant "unreachable"
    modifyDev fun d => { d with incomingPort := port }   -- ntohs(inet_sk(new4)->inet_sport)
  sockFree old4
  sockFree old6

/-- `inet_sk_get_local_port_range` for a kernel socket (no
    `IP_LOCAL_PORT_RANGE`): the netns default `32768..60999`
    (af_inet.c:1803). -/
def LOCAL_PORT_LOW : Nat := 32768
def LOCAL_PORT_HIGH : Nat := 60999

/-- `udp_lib_get_port`'s first candidate for a random port (udp.c:254-258):
    `reciprocal_scale(rand, remaining) + low`. -/
def randomPortFirst (rand : Nat) : Nat :=
  LOCAL_PORT_LOW + (rand * (LOCAL_PORT_HIGH - LOCAL_PORT_LOW + 1)) / 2 ^ 32

/-- wg_socket_init (socket.c:349-417), a cut point (see the module note).
    For port 0 the IPv4 bind draws one `get_random_u32` (udp.c:257, the
    `.udpPortDraw` record) and binds its first candidate; a candidate that a
    conflicting socket holds makes the C step through the UDP hash table
    (a stepping that depends on the boot-time table size), which is outside
    the domain. The IPv6 socket then binds the same port `v6only`, which
    conflicts with no fixture socket at a port the IPv4 bind got. -/
def socketInit (port : Nat) : M Int := do
  let d ← getDev
  -- `creating_net` is NULL only after wg_destruct or wg_netns_pre_exit
  if !d.creatingNet then unsupported "wg_socket_init without creating_net (-ENONET)"
  let bound := (← get).portBound
  -- wg0's own sockets, bound to the wildcard addresses while running
  let held (p : Nat) : Bool := bound p || d.sock4 == some p || d.sock6 == some p
  let chosen ← do
    if port == 0 then
      let bs ← hidden .udpPortDraw
      let rand := bs.foldr (fun b acc => acc * 256 + b.toNat) 0
      let first := randomPortFirst rand
      if held first then unsupported "the random port draw collides with a bound port"
      pure first
    else
      -- udp_sock_create4 fails; pr_err (loglevel 3, no record); goto out
      if held port then return -EADDRINUSE
      pure port
  -- ipv6_mod_enabled(); the IPv6 socket at `chosen`, v6only: no conflict
  socketReinit (some chosen) (some chosen)
  return 0

end Leanux.WG
