"""WireGuard configuration operations: trace validation, attribute encoding,
and decoding of WG_CMD_GET_DEVICE dumps into a canonical device state.

The trace carries a structured configuration; this module encodes it as the
generic-netlink attribute payload of WG_CMD_SET_DEVICE (include/uapi/linux/
wireguard.h), which the guest sends after the family and generic-netlink
headers. The guest returns each dump message's attribute payload; `decode_dump`
coalesces them as the UAPI instructs receivers to (a peer continued across
messages repeats its public key), producing the canonical state that the
mirror computes directly.

Keys and addresses are lowercase hex of their bytes in network order: 4 bytes
for IPv4, 16 for IPv6.
"""
import re
import struct

IFNAME = "wg0"
KEY_LEN = 32
NLA_F_NESTED = 1 << 15
NLA_TYPE_MASK = ~((1 << 15) | (1 << 14)) & 0xffff

# enum wgdevice_attribute / wgpeer_attribute / wgallowedip_attribute
DEV_IFINDEX, DEV_IFNAME, DEV_PRIVATE_KEY, DEV_PUBLIC_KEY, DEV_FLAGS, DEV_LISTEN_PORT, DEV_FWMARK, DEV_PEERS = range(1, 9)
(PEER_PUBLIC_KEY, PEER_PRESHARED_KEY, PEER_FLAGS, PEER_ENDPOINT, PEER_KEEPALIVE, PEER_LAST_HANDSHAKE,
 PEER_RX_BYTES, PEER_TX_BYTES, PEER_ALLOWEDIPS, PEER_PROTOCOL_VERSION) = range(1, 11)
AIP_FAMILY, AIP_IPADDR, AIP_CIDR = range(1, 4)
DEVICE_F_REPLACE_PEERS = 1
PEER_F_REMOVE_ME, PEER_F_REPLACE_ALLOWEDIPS, PEER_F_UPDATE_ONLY = 1, 2, 4
AF_INET, AF_INET6 = 2, 10

CONFIG_FIELDS = {"private_key", "listen_port", "fwmark", "replace_peers", "peers"}
PEER_FIELDS = {"public_key", "remove", "update_only", "replace_allowed_ips", "preshared_key",
               "endpoint", "keepalive", "allowed_ips"}


class InvalidConfig(ValueError):
    pass


def _key(value, where):
    if type(value) is not str or not re.fullmatch(r"[0-9a-f]{64}", value):
        raise InvalidConfig(f"{where}: expected 64 lowercase hex digits")
    return bytes.fromhex(value)


def _int(value, low, high, where):
    if type(value) is not int or not low <= value <= high:
        raise InvalidConfig(f"{where}: expected integer in [{low}, {high}]")
    return value


def _bool(value, where):
    if type(value) is not bool:
        raise InvalidConfig(f"{where}: expected boolean")
    return value


def _address(entry, where, with_port):
    fields = {"family", "addr", "port"} if with_port else {"family", "addr", "cidr"}
    if type(entry) is not dict or set(entry) != fields:
        raise InvalidConfig(f"{where}: expected exactly {sorted(fields)}")
    family = entry["family"]
    if family not in (4, 6):
        raise InvalidConfig(f"{where}.family: expected 4 or 6")
    digits = 8 if family == 4 else 32
    addr = entry["addr"]
    if type(addr) is not str or not re.fullmatch(f"[0-9a-f]{{{digits}}}", addr):
        raise InvalidConfig(f"{where}.addr: expected {digits} lowercase hex digits")
    if with_port:
        _int(entry["port"], 0, 65535, f"{where}.port")
    else:
        _int(entry["cidr"], 0, 255, f"{where}.cidr")   # the kernel rejects > 32/128, observably
    return bytes.fromhex(addr)


def validate_config(config, where="config"):
    if type(config) is not dict or not set(config) <= CONFIG_FIELDS:
        raise InvalidConfig(f"{where}: fields must be a subset of {sorted(CONFIG_FIELDS)}")
    if "private_key" in config:
        _key(config["private_key"], f"{where}.private_key")
    if "listen_port" in config:
        _int(config["listen_port"], 0, 65535, f"{where}.listen_port")
    if "fwmark" in config:
        _int(config["fwmark"], 0, 2**32 - 1, f"{where}.fwmark")
    if "replace_peers" in config:
        _bool(config["replace_peers"], f"{where}.replace_peers")
    peers = config.get("peers", [])
    if type(peers) is not list or len(peers) > 16:
        raise InvalidConfig(f"{where}.peers: expected at most 16 peers")
    for i, peer in enumerate(peers):
        pw = f"{where}.peers[{i}]"
        if type(peer) is not dict or "public_key" not in peer or not set(peer) <= PEER_FIELDS:
            raise InvalidConfig(f"{pw}: needs public_key; fields must be a subset of {sorted(PEER_FIELDS)}")
        _key(peer["public_key"], f"{pw}.public_key")
        for flag in ("remove", "update_only", "replace_allowed_ips"):
            if flag in peer:
                _bool(peer[flag], f"{pw}.{flag}")
        if "preshared_key" in peer:
            _key(peer["preshared_key"], f"{pw}.preshared_key")
        if "endpoint" in peer:
            _address(peer["endpoint"], f"{pw}.endpoint", True)
        if "keepalive" in peer:
            _int(peer["keepalive"], 0, 65535, f"{pw}.keepalive")
        ips = peer.get("allowed_ips", [])
        if type(ips) is not list or len(ips) > 32:
            raise InvalidConfig(f"{pw}.allowed_ips: expected at most 32 entries")
        for j, ip in enumerate(ips):
            _address(ip, f"{pw}.allowed_ips[{j}]", False)
    return config


def _attr(kind, data, nested=False):
    header = struct.pack("=HH", 4 + len(data), kind | (NLA_F_NESTED if nested else 0))
    return header + data + b"\0" * (-len(data) % 4)


def _sockaddr(endpoint):
    addr = bytes.fromhex(endpoint["addr"])
    if endpoint["family"] == 4:   # struct sockaddr_in
        return struct.pack("=H", AF_INET) + struct.pack("!H", endpoint["port"]) + addr + b"\0" * 8
    # struct sockaddr_in6: family, port, flowinfo, addr, scope_id
    return struct.pack("=H", AF_INET6) + struct.pack("!HI", endpoint["port"], 0) + addr + struct.pack("=I", 0)


def encode_set(config):
    """Attribute payload of WG_CMD_SET_DEVICE for `wg0`."""
    validate_config(config)
    out = _attr(DEV_IFNAME, IFNAME.encode() + b"\0")
    if config.get("replace_peers"):
        out += _attr(DEV_FLAGS, struct.pack("=I", DEVICE_F_REPLACE_PEERS))
    if "private_key" in config:
        out += _attr(DEV_PRIVATE_KEY, bytes.fromhex(config["private_key"]))
    if "listen_port" in config:
        out += _attr(DEV_LISTEN_PORT, struct.pack("=H", config["listen_port"]))
    if "fwmark" in config:
        out += _attr(DEV_FWMARK, struct.pack("=I", config["fwmark"]))
    if "peers" in config:
        peers = b""
        for peer in config["peers"]:
            body = _attr(PEER_PUBLIC_KEY, bytes.fromhex(peer["public_key"]))
            flags = (PEER_F_REMOVE_ME if peer.get("remove") else 0) | \
                    (PEER_F_UPDATE_ONLY if peer.get("update_only") else 0) | \
                    (PEER_F_REPLACE_ALLOWEDIPS if peer.get("replace_allowed_ips") else 0)
            if flags:
                body += _attr(PEER_FLAGS, struct.pack("=I", flags))
            if "preshared_key" in peer:
                body += _attr(PEER_PRESHARED_KEY, bytes.fromhex(peer["preshared_key"]))
            if "endpoint" in peer:
                body += _attr(PEER_ENDPOINT, _sockaddr(peer["endpoint"]))
            if "keepalive" in peer:
                body += _attr(PEER_KEEPALIVE, struct.pack("=H", peer["keepalive"]))
            if "allowed_ips" in peer:
                ips = b""
                for ip in peer["allowed_ips"]:
                    family = AF_INET if ip["family"] == 4 else AF_INET6
                    entry = _attr(AIP_FAMILY, struct.pack("=H", family)) + \
                        _attr(AIP_IPADDR, bytes.fromhex(ip["addr"])) + \
                        _attr(AIP_CIDR, struct.pack("=B", ip["cidr"]))
                    ips += _attr(0, entry, nested=True)
                body += _attr(PEER_ALLOWEDIPS, ips, nested=True)
            peers += _attr(0, body, nested=True)
        out += _attr(DEV_PEERS, peers, nested=True)
    return out


def encode_get():
    """Attribute payload of WG_CMD_GET_DEVICE (a dump) for `wg0`."""
    return _attr(DEV_IFNAME, IFNAME.encode() + b"\0")


def _attrs(data, where):
    result, offset = [], 0
    while offset < len(data):
        if offset + 4 > len(data):
            raise InvalidConfig(f"{where}: truncated attribute header")
        length, kind = struct.unpack_from("=HH", data, offset)
        if length < 4 or offset + length > len(data):
            raise InvalidConfig(f"{where}: attribute length {length}")
        result.append((kind & NLA_TYPE_MASK, data[offset + 4:offset + length]))
        offset += (length + 3) & ~3
    return result


def _fixed(value, fmt, where):
    if len(value) != struct.calcsize(fmt):
        raise InvalidConfig(f"{where}: length {len(value)}")
    return struct.unpack(fmt, value)


def _bytes(value, length, where):
    if len(value) != length:
        raise InvalidConfig(f"{where}: length {len(value)}")
    return value.hex()


def _set(target, key, value, where):
    if key in target:
        raise InvalidConfig(f"{where}: duplicate {key}")
    target[key] = value


def _decode_endpoint(data):
    if len(data) < 2:
        raise InvalidConfig("endpoint: truncated")
    family = struct.unpack_from("=H", data)[0]
    if family == AF_INET and len(data) == 16:
        return {"family": 4, "addr": data[4:8].hex(), "port": struct.unpack_from("!H", data, 2)[0]}
    if family == AF_INET6 and len(data) == 28:
        # W5 (2.5): the scope id (host order), nonzero for a link-local endpoint
        return {"family": 6, "addr": data[8:24].hex(), "port": struct.unpack_from("!H", data, 2)[0],
                "scope": struct.unpack_from("=I", data, 24)[0]}
    raise InvalidConfig(f"endpoint family {family} length {len(data)}")


def _decode_allowed_ip(entry):
    ip = {}
    for k, v in _attrs(entry, "allowedip"):
        if k == AIP_FAMILY:
            family = _fixed(v, "=H", "allowedip.family")[0]
            if family not in (AF_INET, AF_INET6):
                raise InvalidConfig(f"allowedip.family {family}")
            _set(ip, "family", 4 if family == AF_INET else 6, "allowedip")
        elif k == AIP_IPADDR:
            _set(ip, "addr", v, "allowedip")
        elif k == AIP_CIDR:
            _set(ip, "cidr", _fixed(v, "=B", "allowedip.cidr")[0], "allowedip")
        else:
            raise InvalidConfig(f"unknown allowed IP attribute {k}")
    if set(ip) != {"family", "addr", "cidr"}:
        raise InvalidConfig(f"incomplete allowed IP {sorted(ip)}")
    ip["addr"] = _bytes(ip["addr"], 4 if ip["family"] == 4 else 16, "allowedip.addr")
    return ip


def _decode_peer(data):
    peer, seen = {"allowed_ips": []}, set()
    for kind, value in _attrs(data, "peer"):
        if kind in seen:
            raise InvalidConfig(f"peer: duplicate attribute {kind}")
        seen.add(kind)
        if kind == PEER_PUBLIC_KEY:
            peer["public_key"] = _bytes(value, KEY_LEN, "peer.public_key")
        elif kind == PEER_PRESHARED_KEY:
            peer["preshared_key"] = _bytes(value, KEY_LEN, "peer.preshared_key")
        elif kind == PEER_ENDPOINT:
            peer["endpoint"] = _decode_endpoint(value)
        elif kind == PEER_KEEPALIVE:
            peer["keepalive"] = _fixed(value, "=H", "peer.keepalive")[0]
        elif kind == PEER_LAST_HANDSHAKE:
            peer["last_handshake"] = list(_fixed(value, "=qq", "peer.last_handshake"))
        elif kind == PEER_RX_BYTES:
            peer["rx_bytes"] = _fixed(value, "=Q", "peer.rx_bytes")[0]
        elif kind == PEER_TX_BYTES:
            peer["tx_bytes"] = _fixed(value, "=Q", "peer.tx_bytes")[0]
        elif kind == PEER_PROTOCOL_VERSION:
            peer["protocol_version"] = _fixed(value, "=I", "peer.protocol_version")[0]
        elif kind == PEER_ALLOWEDIPS:
            peer["allowed_ips"] = [_decode_allowed_ip(entry) for _, entry in _attrs(value, "allowedips")]
        else:
            raise InvalidConfig(f"unknown peer attribute {kind}")
    if "public_key" not in peer:
        raise InvalidConfig("peer without public key")
    return peer, seen


DEVICE_FIELDS = {DEV_IFINDEX: ("ifindex", "=I"), DEV_LISTEN_PORT: ("listen_port", "=H"), DEV_FWMARK: ("fwmark", "=I")}


def decode_dump(payloads):
    """Coalesce the attribute payloads of a WG_CMD_GET_DEVICE dump into one
    canonical device state. Anything the kernel's get_device_dump/get_peer
    would not produce (unknown or repeated attributes, wrong lengths, a
    continued peer carrying more than its key and allowed IPs) is rejected."""
    try:
        return _decode_dump(payloads)
    except (struct.error, UnicodeDecodeError) as exc:
        raise InvalidConfig(f"malformed dump: {exc}") from exc


def _decode_dump(payloads):
    if type(payloads) is not list or not payloads:
        raise InvalidConfig("dump without messages")
    device, peers = {}, []
    for index, payload in enumerate(payloads):
        if type(payload) is not str or not re.fullmatch(r"([0-9a-f]{2})*", payload):
            raise InvalidConfig(f"dump[{index}]: payload must be lowercase hex")
        first_peer, seen = True, set()
        for kind, value in _attrs(bytes.fromhex(payload), f"dump[{index}]"):
            if kind in seen:
                raise InvalidConfig(f"dump[{index}]: duplicate attribute {kind}")
            seen.add(kind)
            if kind in DEVICE_FIELDS:
                key, fmt = DEVICE_FIELDS[kind]
                _set(device, key, _fixed(value, fmt, key)[0], "device")
            elif kind == DEV_IFNAME:
                if not value.endswith(b"\0") or b"\0" in value[:-1]:
                    raise InvalidConfig("device.ifname: not a NUL-terminated string")
                _set(device, "ifname", value[:-1].decode(), "device")
            elif kind == DEV_PRIVATE_KEY:
                _set(device, "private_key", _bytes(value, KEY_LEN, "device.private_key"), "device")
            elif kind == DEV_PUBLIC_KEY:
                _set(device, "public_key", _bytes(value, KEY_LEN, "device.public_key"), "device")
            elif kind == DEV_PEERS:
                for _, entry in _attrs(value, "peers"):
                    peer, attributes = _decode_peer(entry)
                    continued = first_peer and index > 0 and peers and peers[-1]["public_key"] == peer["public_key"]
                    if continued:
                        if attributes - {PEER_PUBLIC_KEY, PEER_ALLOWEDIPS}:
                            raise InvalidConfig(f"dump[{index}]: continued peer repeats attributes")
                        peers[-1]["allowed_ips"] += peer["allowed_ips"]
                    else:
                        peers.append(peer)
                    first_peer = False
            else:
                raise InvalidConfig(f"unknown device attribute {kind}")
    device["peers"] = peers
    return device


# Stage B1: datagrams routed into wg0 from the fixture's UDP socket; D2
# adds their UDP payload.
PACKET_FIELDS = {"family", "dst"}
PACKET_OPTIONAL = {"payload"}
# wg0's MTU (1420) less the IPv4 and UDP headers: an IPv4 packet that fits.
# IPv6 payloads above 1372 do not fit either; the mirror's environment places
# them outside the domain (Env.xmitPacket).
MAX_XMIT_PAYLOAD = 1392
# IPv6 payloads above 1372 exceed the MTU (1420 - 40 - 8) and fragment at the
# source (IPV6_PMTUDISC_WANT): outside the mirror's domain, so invalid input.
MAX_XMIT_PAYLOAD6 = 1372


def validate_packet(packet, where="packet"):
    """A UDP datagram to `dst` (hex bytes of an IPv4 or IPv6 address), sent
    from the fixture's dual-stack socket; the routes the fixture adds at
    `wg_up` send every non-local destination into wg0. `payload` (D2), 1 to
    1392 bytes of lowercase hex, is the datagram; without it the datagram is
    the fixture's historic 4 bytes "leux". A packet with a payload may not go
    to an IPv6 link-local destination (fe80::/10): wg0's link-local source
    address is random, so its bytes are not determined."""
    if type(packet) is not dict or not PACKET_FIELDS <= set(packet) <= PACKET_FIELDS | PACKET_OPTIONAL:
        raise InvalidConfig(f"{where}: expected {sorted(PACKET_FIELDS)} and optionally {sorted(PACKET_OPTIONAL)}")
    if packet["family"] not in (4, 6):
        raise InvalidConfig(f"{where}.family: expected 4 or 6")
    digits = 8 if packet["family"] == 4 else 32
    if type(packet["dst"]) is not str or not re.fullmatch(f"[0-9a-f]{{{digits}}}", packet["dst"]):
        raise InvalidConfig(f"{where}.dst: expected {digits} lowercase hex digits")
    dst = bytes.fromhex(packet["dst"])
    # Destinations the sender's IP layer handles before routing never reach
    # wg0: loopback and the fixture's own addresses (local), 0.0.0.0/8
    # (EINVAL, or rewritten to loopback), the limited broadcast (EACCES), ::
    # (rewritten to ::1), and v4-mapped addresses (the IPv4 path).
    if packet["family"] == 4 and (dst[0] in (0, 127) or dst == b"\xff" * 4 or dst == bytes.fromhex(FIXTURE_ADDR4)):
        raise InvalidConfig(f"{where}.dst: an address the sender does not route into wg0")
    if packet["family"] == 6 and (dst in (bytes(16), bytes(15) + b"\x01", bytes.fromhex(FIXTURE_ADDR6),
                                          bytes.fromhex(FIXTURE_LINK_LOCAL6))
                                  or dst[:12] == bytes(10) + b"\xff\xff"):
        raise InvalidConfig(f"{where}.dst: an address the sender does not route into wg0")
    if "payload" in packet:
        payload = packet["payload"]
        if type(payload) is not str or not re.fullmatch(f"(?:[0-9a-f]{{2}}){{1,{MAX_XMIT_PAYLOAD}}}", payload):
            raise InvalidConfig(f"{where}.payload: expected 1 to {MAX_XMIT_PAYLOAD} bytes of lowercase hex")
        if packet["family"] == 6 and len(payload) > 2 * MAX_XMIT_PAYLOAD6:
            raise InvalidConfig(f"{where}.payload: IPv6 payloads are at most {MAX_XMIT_PAYLOAD6} bytes (no fragmentation)")
        if packet["family"] == 6 and dst[0] == 0xfe and dst[1] & 0xc0 == 0x80:
            raise InvalidConfig(f"{where}.dst: a link-local destination (wg0's source address is random)")
    return packet


FIXTURE_ADDR4 = "0afffe01"                             # 10.255.254.1/32 on wg0
FIXTURE_ADDR6 = "fd00ffff000000000000000000000001"     # fd00:ffff::1/128 on wg0
FIXTURE_LINK_LOCAL6 = "fe8000000000000000000000ffff0001"   # fe80::ffff:1/64 on lo (W5)


def encode_packet(packet):
    """The guest's sockaddr_in6 address (IPv4 destinations as v4-mapped),
    followed by the payload, if any."""
    validate_packet(packet)
    dst = bytes.fromhex(packet["dst"])
    address = bytes(10) + b"\xff\xff" + dst if packet["family"] == 4 else dst
    return packet["family"], address + bytes.fromhex(packet.get("payload", ""))
