#!/usr/bin/env python3
"""Writes the A1 allocation-outcome traces into corpus/alloc
(docs/2026-10-05-a-alloc.md, section 7).

A1 steers the class-(a) sites only [USER A1]: the three GFP_ATOMIC alloc_skb
calls. Each is an `__alloc_skb` helper site with two encounters on success
(the sk_buff, then the data buffer), so a schedule naming a site lists every
encounter of it in the trace: `fail` fails the sk_buff, `draw, fail` the
data buffer, `draw, draw` lets a success through recorded. The chunk holding
such a trace is armed with the `__alloc_skb`/`kmalloc_reserve` ranges, so
every allocation through them is recorded and consumed by the mirror.

`replySkb` (socket.c:217, cookie replies under load) is not reachable on this
base: the mirror stops at `under_load` (Receive.lean). Its trace,
`a_reply_nomem`, is pending stream E-B.

A2 [USER 2026-10-06] steers the task-context (b-task) sites as a declared
failslab-style extension: each such trace carries "domain_extension":
"failslab". The NULL is in the allocator's output set (the OOM-victim path),
but the forced trace as a whole is not a possible Linux execution (a victim
does not run its next syscall). The FS traces load their schedule on their
own KCOV instance (the guest, A2); a schedule lists every encounter of the
sites it names.

The output is deterministic: rerunning this script reproduces the files.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from harness import noise  # noqa: E402

DEVICE = b"\x11" * 32
INITIATOR = b"\x22" * 32
PORT = 51820
LISTENER = {"family": 4, "addr": "7f000001", "port": 51999}
FAIL = "00" * 8
OBSERVE = {"op": "wg_observe"}
GET = {"op": "wg_get"}
SENDBUF_NOMEM = "wg_socket_send_buffer_to_peer.no_mem"
KEEPALIVE_NOMEM = "wg_packet_send_keepalive.no_mem"


def init(ephemeral=0x33, stamp=1, index=7):
    return noise.initiation(noise.public_key(DEVICE), INITIATOR, bytes([ephemeral]) * 32,
                            bytes(11) + bytes([stamp]), index)


def peer(**extra):
    p = {"public_key": noise.public_key(INITIATOR).hex(),
         "allowed_ips": [{"family": 4, "addr": "0a000000", "cidr": 8}]}
    p.update(extra)
    return p


def setup(**extra):
    return [{"op": "wg_set", "config": {"private_key": DEVICE.hex(), "listen_port": PORT, "peers": [peer(**extra)]}},
            {"op": "wg_up"}]


def inject(message, family=4):
    return {"op": "wg_inject", "family": family, "port": PORT, "message": message.hex()}


XMIT = {"op": "wg_xmit", "packet": {"family": 4, "dst": "0a000001"}}

# name: (ops, steer, expect[, rlimit_nofile])
TRACES = {
    # wg0 initiates (wg_xmit with no session queues the initiation; the send
    # worker's alloc_skb at socket.c:192): recorded unsteered, then each failure
    "a_sendbuf_init_draw": (setup(endpoint=LISTENER) + [XMIT, OBSERVE, GET],
                            [["sendBufSkb", "draw"], ["sendBufSkb", "draw"]], [f"{SENDBUF_NOMEM}=0"]),
    "a_sendbuf_init_nomem": (setup(endpoint=LISTENER) + [XMIT, OBSERVE, GET],
                             [["sendBufSkb", FAIL]], [f"{SENDBUF_NOMEM}=1"]),
    "a_sendbuf_nodata": (setup(endpoint=LISTENER) + [XMIT, OBSERVE, GET],
                         [["sendBufSkb", "draw"], ["sendBufSkb", FAIL]], [f"{SENDBUF_NOMEM}=1"]),
    # wg0 responds (the receive worker): the session is begun and
    # last_sent_handshake set before the send fails; tx_bytes stays 0
    "a_sendbuf_nomem": ([*setup(), inject(init()), OBSERVE, GET],
                        [["sendBufSkb", FAIL]], [f"{SENDBUF_NOMEM}=1", "wg_noise_handshake_begin_session.initiator=0"]),
    "a_sendbuf_resp_nodata": ([*setup(), inject(init(), 6), OBSERVE, GET],
                              [["sendBufSkb", "draw"], ["sendBufSkb", FAIL]], [f"{SENDBUF_NOMEM}=1"]),
    # a failed response, then a newer initiation whose response goes out
    "a_sendbuf_resp_retry": ([*setup(), inject(init()), OBSERVE, inject(init(ephemeral=0x34, stamp=2, index=9)),
                              OBSERVE, GET],
                             [["sendBufSkb", FAIL], ["sendBufSkb", "draw"], ["sendBufSkb", "draw"]],
                             [f"{SENDBUF_NOMEM}=1", f"{SENDBUF_NOMEM}=0"]),
    # the staged keepalive of wg_up (persistent keepalive set before up;
    # send.c:226 in the syscall): no keepalive staged, no initiation queued
    "a_keepalive_nomem": (setup(endpoint=LISTENER, keepalive=25) + [OBSERVE, GET],
                          [["keepaliveSkb", FAIL]], [f"{KEEPALIVE_NOMEM}=1"]),
    "a_keepalive_nodata": (setup(endpoint=LISTENER, keepalive=25) + [OBSERVE, GET],
                           [["keepaliveSkb", "draw"], ["keepaliveSkb", FAIL]], [f"{KEEPALIVE_NOMEM}=1"]),
    # a recorded keepalive allocation: the staged keepalive queues the
    # initiation, whose send-buffer allocation is armed and consumed too
    "a_keepalive_draw": (setup(endpoint=LISTENER, keepalive=25) + [OBSERVE, GET],
                         [["keepaliveSkb", "draw"], ["keepaliveSkb", "draw"]], [f"{KEEPALIVE_NOMEM}=0"]),
    # the staged keepalive of a wg_set that turns persistent keepalive on
    # while wg0 is up
    "a_keepalive_set_nomem": (setup(endpoint=LISTENER) + [
        {"op": "wg_set", "config": {"peers": [{"public_key": noise.public_key(INITIATOR).hex(), "keepalive": 25}]}},
        OBSERVE, GET], [["keepaliveSkb", FAIL]], [f"{KEEPALIVE_NOMEM}=1"]),
}


# ---- A2: the (b-task) sites, under the declared failslab-style extension ----
def eventfd(init=0, flags=2048):
    return {"op": "eventfd2", "init": init, "flags": flags}


def ref(i):
    return {"ref": i}


def dup3(old, new, flags=0):
    return {"op": "dup3", "fd": old, "newfd": {"literal": new}, "flags": flags}


def read(fd):
    return {"op": "read", "fd": fd, "count": 8}


EVENTFD_NOMEM = "do_eventfd.kmalloc_failed"
FILE_ERROR = "do_eventfd.file_error"
# rlimit 128: dup3 to fd 100 grows the table to 128 slots (a 1 KiB fd array,
# one slab call, below the 8 KiB kvmalloc refusal)
FD_HIGH = 100
PEER2 = b"\x44" * 32


def wg_config(peers):
    return {"op": "wg_set", "config": {"private_key": DEVICE.hex(), "listen_port": PORT, "peers": peers}}


def wg_peer(key, ips):
    return {"public_key": noise.public_key(key).hex(),
            "allowed_ips": [{"family": 4, "addr": a, "cidr": c} for a, c in ips]}


# name: (ops, steer, expect[, rlimit_nofile]); a fail in each, so each
# declares the extension
TRACES_A2 = {
    # kmalloc(ctx) fails: -ENOMEM before any fd is reserved; the next
    # eventfd2 gets fd 8
    "a2_eventfd_nomem": ([eventfd(1), eventfd(2), read(ref(1))],
                         [["kmallocEventfdCtx", FAIL], ["kmallocEventfdCtx", "draw"]],
                         [f"{EVENTFD_NOMEM}=1", f"{EVENTFD_NOMEM}=0"]),
    # alloc_empty_file fails after the dentry: alloc_file_pseudo's path_put,
    # __anon_inode_getfile's iput, do_eventfd's put_unused_fd and
    # eventfd_free_ctx; the reserved fd is released, so the next eventfd2
    # gets fd 8 again (A-M6)
    "a2_filp_nomem": ([eventfd(1), eventfd(2), eventfd(3), read(ref(1)), read(ref(2))],
                      [["filpAlloc", FAIL], ["filpAlloc", "draw"], ["filpAlloc", "draw"]],
                      ["alloc_empty_file.zalloc_failed=1", f"{FILE_ERROR}=1", f"{FILE_ERROR}=0"]),
    # d_alloc_pseudo fails: alloc_path_pseudo's -ENOMEM, the same unwind
    # without a file
    "a2_dentry_nomem": ([eventfd(1), eventfd(2), read(ref(1))],
                        [["dAllocPseudo", FAIL], ["dAllocPseudo", "draw"]],
                        ["alloc_path_pseudo.d_alloc_failed=1", f"{FILE_ERROR}=1"]),
    # the second eventfd2's file fails: fd 9 is reserved and released, so
    # the third gets 9, not 10
    "a2_filp_nomem_second": ([eventfd(1), eventfd(2), eventfd(3), read(ref(0)), read(ref(2))],
                             [["filpAlloc", "draw"], ["filpAlloc", FAIL], ["filpAlloc", "draw"]],
                             ["alloc_empty_file.zalloc_failed=1", f"{FILE_ERROR}=1"]),
    # the fd table's three allocations (alloc_fdtable, file.c:147/151/156):
    # dup3 to a high fd returns expand_files' -ENOMEM as is
    # (ksys_dup3.expand_error, not the EMFILE->EBADF mapping); the table is
    # not replaced, so a retry grows it and succeeds (A-M5)
    "a2_fdtable_nomem": ([eventfd(1), dup3(ref(0), FD_HIGH), dup3(ref(0), FD_HIGH), read({"literal": FD_HIGH})],
                         [["kmallocFdtable", FAIL], ["kmallocFdtable", "draw"]],
                         ["alloc_fdtable.kmalloc_failed=1", "ksys_dup3.expand_error=1"], 128),
    "a2_fdarray_nomem": ([eventfd(1), dup3(ref(0), FD_HIGH), dup3(ref(0), FD_HIGH), read({"literal": FD_HIGH})],
                         [["kvmallocFdArray", FAIL], ["kvmallocFdArray", "draw"]],
                         ["alloc_fdtable.fd_array_failed=1", "ksys_dup3.expand_error=1"], 128),
    "a2_fdbitmap_nomem": ([eventfd(1), dup3(ref(0), FD_HIGH), dup3(ref(0), FD_HIGH), read({"literal": FD_HIGH})],
                          [["kvmallocFdBitmaps", FAIL], ["kvmallocFdBitmaps", "draw"]],
                          ["alloc_fdtable.bitmaps_failed=1", "ksys_dup3.expand_error=1"], 128),
    # a failed growth leaves the small table: an fd below 64 still dup3s
    "a2_fdarray_nomem_low": ([eventfd(1), dup3(ref(0), FD_HIGH), dup3(ref(0), 40), read({"literal": 40})],
                             [["kvmallocFdArray", FAIL]],
                             ["alloc_fdtable.fd_array_failed=1"], 128),
    # alloc_fd's expansion (get_unused_fd_flags): 56 eventfd2s fill fds
    # 8-63, the 57th needs fd 64 and the table's kmalloc fails: alloc_fd
    # returns -ENOMEM (alloc_fd.expand_error), do_eventfd frees the context
    # (do_eventfd.fd_error); the next eventfd2 grows the table and gets 64
    "a2_allocfd_nomem": ([eventfd(1)] * 57 + [eventfd(2), read({"literal": 64})],
                         [["kmallocFdtable", FAIL], ["kmallocFdtable", "draw"]],
                         ["alloc_fd.expand_error=1", "do_eventfd.fd_error=1"], 128),
    # wg_set with two peers, the second's kmem_cache_zalloc (peer.c:33)
    # fails: set_peer returns PTR_ERR, wg_set_device stops with -ENOMEM; the
    # first peer (and its allowed ips) stays, as wg_get shows (A-M1)
    "a2_peer_nomem": ([wg_config([wg_peer(INITIATOR, [("0a000000", 8)]), wg_peer(PEER2, [("c0a80000", 16)])]), GET],
                      [["kmemCacheZallocPeer", "draw"], ["kmemCacheZallocPeer", FAIL]],
                      ["wg_peer_create.no_mem=1"]),
    # the first peer fails: no peer at all, the device's key and port set
    "a2_peer_nomem_first": ([wg_config([wg_peer(INITIATOR, [("0a000000", 8)])]), GET],
                            [["kmemCacheZallocPeer", FAIL]], ["wg_peer_create.no_mem=1"]),
    # allowed ips (add, allowedips.c:190/205/234): the root node
    "a2_allowedips_root_nomem": ([wg_config([wg_peer(INITIATOR, [("0a000000", 8), ("c0a80000", 16)])]), GET],
                                 [["allocNode190", FAIL]], ["add.root_no_mem=1"]),
    # a new node below the root's prefix (10.1.0.0/16 under 10.0.0.0/8: no
    # split, the second allocation, :205)
    "a2_allowedips_newnode_nomem": ([wg_config([wg_peer(INITIATOR, [("0a000000", 8), ("0a010000", 16)])]), GET],
                                    [["allocNode205", FAIL]], ["add.newnode_no_mem=1"]),
    # 192.168.0.0/16 beside 10.0.0.0/8 needs an intermediate node (:205 then
    # :234); :234 fails: newnode is unlinked from the peer's list and freed,
    # the trie unchanged (A-M9: the dump would show the freed node)
    "a2_allowedips_split_nomem": ([wg_config([wg_peer(INITIATOR, [("0a000000", 8), ("c0a80000", 16)])]), GET],
                                  [["allocNode234", FAIL]], ["add.intermediate_no_mem=1"]),
    # a split that succeeds, then a later insert's split fails: the first
    # intermediate node stays
    "a2_allowedips_split_second": ([wg_config([wg_peer(INITIATOR, [("0a000000", 8), ("c0a80000", 16),
                                                                   ("ac100000", 12)])]), GET],
                                   [["allocNode234", "draw"], ["allocNode234", FAIL]],
                                   ["add.intermediate_no_mem=1", "add.intermediate_no_mem=0"]),
}


# Pipes (A section 19.6; D3+A integration [AGENT]): the three direct pipe
# sites, each failed once under the extension. pipe2 is nonblocking, so no
# read waits; a failed pipe2's ends resolve to -1, so the later operations
# use the second pipe.
def pipe2():
    return {"op": "pipe2", "flags": 2048}


def pwrite(p, count, value="7"):
    return {"op": "write", "fd": {"pipe": p, "end": 1}, "count": count, "value": value}


def pread(p, count):
    return {"op": "read", "fd": {"pipe": p, "end": 0}, "count": count}


TRACES_A2.update({
    # alloc_pipe_info's kzalloc (pipe.c:798) fails: get_pipe_inode's
    # fail_iput, create_pipe_files' -ENFILE; the next pipe2 succeeds
    "a2_pipe_info_nomem": ([pipe2(), pipe2(), pwrite(1, 8), pread(1, 8)],
                           [["kzallocPipeInfo", FAIL], ["kzallocPipeInfo", "draw"]],
                           ["alloc_pipe_info.kzalloc_failed=1", "get_pipe_inode.no_pipe=1"]),
    # the buffers' kcalloc (:815) fails: out_revert_acct undoes the
    # accounting (A-M7: the next pipe2's user_bufs operands show it), -ENFILE
    "a2_pipe_bufs_nomem": ([pipe2(), pipe2(), pwrite(1, 8), pread(1, 8)],
                           [["kzallocPipeInfo", "draw"], ["kcallocPipeBufs", FAIL],
                            ["kzallocPipeInfo", "draw"], ["kcallocPipeBufs", "draw"]],
                           ["alloc_pipe_info.bufs_allocated=0", "get_pipe_inode.no_pipe=1"]),
    # pipe_write's first page (:513) fails: nothing written, -ENOMEM; the
    # retry allocates (tmp_page is still NULL) and writes
    "a2_pipe_page_nomem": ([pipe2(), pwrite(0, 8), pwrite(0, 8), pread(0, 16)],
                           [["allocPipePage", FAIL], ["allocPipePage", "draw"]],
                           ["pipe_write.alloc_failed=1"]),
    # the second page of an 8 KiB write fails: the partial count 4096 is
    # returned (`ret ? : -ENOMEM`, A-M8), the read gets the first page
    "a2_pipe_page_nomem_partial": ([pipe2(), pwrite(0, 8192), pread(0, 8192)],
                                   [["allocPipePage", "draw"], ["allocPipePage", FAIL]],
                                   ["pipe_write.alloc_failed=1"]),
})
# Draw-only controls for the task-instance schedule: every encounter is
# recorded and consumed exactly, nothing forced, so no extension is declared
# (a draw is allowed at any steerable site).
TRACES_A2_DRAW = {
    "a2_eventfd_draw": ([eventfd(1), eventfd(2), read(ref(1))],
                        [["kmallocEventfdCtx", "draw"], ["kmallocEventfdCtx", "draw"]],
                        [f"{EVENTFD_NOMEM}=0"]),
    "a2_fdtable_draw": ([eventfd(1), dup3(ref(0), FD_HIGH), read({"literal": FD_HIGH})],
                        [["kmallocFdtable", "draw"]], ["alloc_fdtable.kmalloc_failed=0"], 128),
}


def main():
    out = ROOT / "corpus/alloc"
    out.mkdir(exist_ok=True)
    groups = [(TRACES, None), (TRACES_A2, "failslab"), (TRACES_A2_DRAW, None)]
    for traces, extension in groups:
        for name, (ops, steer, expect, *rlimit) in traces.items():
            trace = {"version": 1, "id": name, "ops": ops, "steer": steer, "expect": expect}
            if rlimit:
                trace["rlimit_nofile"] = rlimit[0]
            if extension:
                trace["domain_extension"] = extension
            (out / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")
    print(f"wrote {sum(len(t) for t, _ in groups)} traces to {out}")


if __name__ == "__main__":
    main()
