#!/usr/bin/env python3
"""Writes workstream W1's traces (netlink completeness,
docs/2026-10-06-w1-w2-netlink.md section 3.3: one trace per arm of
drivers/net/wireguard/netlink.c that a natural message reaches) into
corpus/wireguard as n1_*.json. Every trace configures a down wg0 (no wg_up:
no datagram leaves, so scoped endpoints stay inert) and reads the device back
with wg_get after each arm, so the observables are the error code (A1), the
dump's data (A1) and the arms' decisions (A2). The output is deterministic.
"""
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from harness import noise  # noqa: E402
from harness.trace import validate_trace  # noqa: E402

_spec = importlib.util.spec_from_file_location("wg_d1_corpus", ROOT / "scripts" / "wg-d1-corpus.py")
d1 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(d1)

KEY = d1.key(d1.DEVICE)
PUB = d1.key(noise.public_key(d1.PEER))
PUB2 = d1.key(noise.public_key(b"\x33" * 32))
V4 = {"family": 4, "addr": "7f000001", "port": 51999}
V6 = {"family": 6, "addr": "00000000000000000000000000000001", "port": 51999}
V4MAPPED = {"family": 6, "addr": "00000000000000000000ffff7f000001", "port": 51999}
AIP4 = {"family": 4, "addr": "0a000000", "cidr": 8}
AIP4B = {"family": 4, "addr": "0a010000", "cidr": 16}
AIP6 = {"family": 6, "addr": "20010db8000000000000000000000000", "cidr": 32}
GET = {"op": "wg_get"}


def wg_set(config, device=None):
    op = {"op": "wg_set", "config": config}
    if device is not None:
        op["device"] = device
    return op


def wg_get(device=None):
    op = {"op": "wg_get"}
    if device is not None:
        op["device"] = device
    return op


def base():
    """wg0 with its key, port and one peer with one allowed IP and the v4 listener."""
    return wg_set({"private_key": KEY, "listen_port": d1.PORT,
                   "peers": [{"public_key": PUB, "allowed_ips": [AIP4], "endpoint": V4}]})


def peer(**extra):
    p = {"public_key": PUB}
    p.update(extra)
    return p


TRACES = {
    # lookup_interface: both or neither selector (-EBADR), on wg_set and wg_get
    "n1_lookup_ebadr": [base(), wg_set({"listen_port": 1}, {}), wg_set({"listen_port": 1}, {"ifname": "wg0", "ifindex": 3}),
                        wg_get({}), wg_get({"ifname": "wg0", "ifindex": 3}), GET],
    # lookup by ifindex: the same device as by name
    "n1_lookup_ifindex": [base(), wg_set({"listen_port": 51821}, {"ifindex": 3}), wg_get({"ifindex": 3}), GET],
    # -ENODEV: an unknown name, index 0, the index after wg0's, a large one
    "n1_lookup_enodev": [base(), wg_set({"listen_port": 1}, {"ifname": "wg1"}), wg_set({"listen_port": 1}, {"ifindex": 0}),
                         wg_set({"listen_port": 1}, {"ifindex": 4}), wg_get({"ifindex": 99}), wg_get({"ifname": "wg9"}), GET],
    # lo: no rtnl_link_ops (-EOPNOTSUPP); sit0: kind "sit" (-EOPNOTSUPP)
    "n1_lookup_lo": [base(), wg_set({"listen_port": 1}, {"ifname": "lo"}), wg_get({"ifindex": 1}), GET],
    "n1_lookup_sit0": [base(), wg_set({"listen_port": 1}, {"ifname": "sit0"}), wg_get({"ifindex": 2}), GET],
    # L interaction: wg0 re-created takes ifindex 4; its old index is gone
    "n1_lookup_recreate": [base(), {"op": "wg_delete"}, {"op": "wg_create"}, wg_set({"listen_port": 1}, {"ifindex": 3}),
                           wg_set({"private_key": KEY, "listen_port": d1.PORT}, {"ifindex": 4}), wg_get({"ifindex": 4}), GET],
    # unknown device flags (-EOPNOTSUPP); flag 1 is replace_peers
    "n1_device_flags": [base(), wg_set({"flags": 2, "listen_port": 1}), GET, wg_set({"flags": 1}), GET],
    # unknown peer flags (-EOPNOTSUPP); the raw flags field
    "n1_peer_flags": [base(), wg_set({"peers": [peer(flags=8)]}), GET, wg_set({"peers": [peer(flags=0)]}), GET],
    # WGPEER_A_PROTOCOL_VERSION: 1 accepted, 2 rejected (-EPFNOSUPPORT)
    "n1_protocol_version": [base(), wg_set({"peers": [peer(protocol_version=1, keepalive=5)]}), GET,
                            wg_set({"peers": [peer(protocol_version=2, keepalive=7)]}), GET],
    # a peer without a public key (-EINVAL): no peer in the dump
    "n1_no_public_key": [wg_set({"private_key": KEY, "listen_port": d1.PORT}),
                         wg_set({"peers": [{"allowed_ips": [AIP4], "endpoint": V4}]}), GET],
    # a peer entry without NLA_F_NESTED: -EINVAL, the earlier peer applied
    "n1_malformed_peer": [wg_set({"private_key": KEY, "listen_port": d1.PORT}),
                          wg_set({"peers": [peer(allowed_ips=[AIP4]), {"public_key": PUB2, "malformed": "not_nested"}]}), GET],
    # an allowed-IP entry without NLA_F_NESTED: -EINVAL, the earlier IPs applied
    "n1_malformed_aip": [wg_set({"private_key": KEY, "listen_port": d1.PORT}),
                         wg_set({"peers": [peer(allowed_ips=[AIP4, dict(AIP4B, malformed="not_nested"), AIP6])]}), GET],
    # a missing allowed-IP attribute (-EINVAL), each of the three
    "n1_aip_missing": [wg_set({"private_key": KEY, "listen_port": d1.PORT}),
                       wg_set({"peers": [peer(allowed_ips=[AIP4, {"family": 4, "addr": "0a010000"}])]}), GET,
                       wg_set({"peers": [peer(allowed_ips=[{"addr": "0a010000", "cidr": 16}])]}), GET,
                       wg_set({"peers": [peer(allowed_ips=[{"family": 4, "cidr": 16}])]}), GET],
    # the family/length/cidr fallthrough (-EINVAL): a 16-byte IPv4 address, a
    # 4-byte IPv6 one, af 0, an 8-byte address, cidr 33 and 129
    "n1_aip_wrong": [wg_set({"private_key": KEY, "listen_port": d1.PORT, "peers": [peer()]}),
                     wg_set({"peers": [peer(allowed_ips=[{"family": 4, "addr": "20010db8000000000000000000000000", "cidr": 8}])]}), GET,
                     wg_set({"peers": [peer(allowed_ips=[{"family": 6, "addr": "0a000000", "cidr": 8}])]}), GET,
                     wg_set({"peers": [peer(allowed_ips=[dict(AIP4, af=0)])]}), GET,
                     wg_set({"peers": [peer(allowed_ips=[{"family": 4, "addr": "0a00000000000000", "cidr": 8}])]}), GET,
                     wg_set({"peers": [peer(allowed_ips=[dict(AIP4, cidr=33)])]}), GET,
                     wg_set({"peers": [peer(allowed_ips=[dict(AIP6, cidr=129)])]}), GET],
    # endpoints set_peer ignores (ret 0, the old endpoint kept): a 28-byte
    # AF_INET, a 16-byte AF_INET6, AF_UNSPEC, a 20-byte one
    "n1_endpoint_ignored": [base(), wg_set({"peers": [peer(endpoint=dict(V4, len=28))]}), GET,
                            wg_set({"peers": [peer(endpoint=dict(V6, len=16))]}), GET,
                            wg_set({"peers": [peer(endpoint=dict(V6, af=0))]}), GET,
                            wg_set({"peers": [peer(endpoint=dict(V4, len=20))]}), GET],
    # sin6_flowinfo and sin6_scope_id are stored and dumped; a scope-only
    # change replaces the endpoint (endpoint_eq compares the scope)
    "n1_flowinfo_scope": [base(), wg_set({"peers": [peer(endpoint=dict(V6, flowinfo=0x12345, scope_id=1))]}), GET,
                          wg_set({"peers": [peer(endpoint=dict(V6, flowinfo=0x12345, scope_id=2))]}), GET],
    # a flowinfo-only change is no change: endpoint_eq ignores flowinfo
    "n1_flowinfo_only": [base(), wg_set({"peers": [peer(endpoint=dict(V6, flowinfo=0x12345, scope_id=1))]}), GET,
                         wg_set({"peers": [peer(endpoint=dict(V6, flowinfo=0x54321, scope_id=1))]}), GET],
    # a v4-mapped IPv6 endpoint is stored as a 28-byte sockaddr_in6
    "n1_v4_mapped": [base(), wg_set({"peers": [peer(endpoint=V4MAPPED)]}), GET],
}


def main():
    out = ROOT / "corpus" / "wireguard"
    for name, ops in TRACES.items():
        trace = {"version": 1, "id": name, "ops": ops}
        validate_trace(trace)
        (out / f"{name}.json").write_text(json.dumps(trace, indent=2) + "\n")
    print(f"wrote {len(TRACES)} traces to {out}")


if __name__ == "__main__":
    main()
